//===-- Constraints.cpp ---------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Constraints.h"

#include <bits/functional_hash.h>
#include <cassert>
#include <map>
#include <set>
#include <utility>

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Function.h"
#else
#include "llvm/Function.h"
#endif
#include "llvm/Support/CommandLine.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/TimerStatIncrementer.h"
#include "klee/SolverStats.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"

#include "klee/Config/Version.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/util/ExprVisitor.h"

using namespace klee;

namespace {
llvm::cl::opt<bool> RewriteEqualities(
    "rewrite-equalities", llvm::cl::init(true),
    llvm::cl::desc("Rewrite existing constraints when an equality with a "
                   "constant is added (default=on)"));
}

uint64_t ConstraintSetView::next_free_position = 1;
uint64_t ConstraintSetView::version_cntr = 1;

void ConstraintSetView::extractAndResetConstraints(ConstraintSetView &other) {
  constraints.swap(other.constraints);
  origPosition.swap(other.origPosition);
//  deletedPositions.swap(other.deletedPositions);
//  std::swap(uid_cntr, other.uid_cntr);
//  std::swap(next_free_position, other.next_free_position);
}

bool ConstraintSetView::operator==(const ConstraintSetView &other) const {
  return constraints == other.constraints;
}

void ConstraintSetView::dump() const {
  size_t i = 0;
  for (const_iterator it = constraints.begin(), itE = constraints.end();
       it != itE; ++it) {
    llvm::errs() << "{" << origPosition[i].constraint_id << "/"<< origPosition[i].constraint_width << "}\n";
    llvm::errs() << "vars:[ ";
    for (auto ar: origPosition[i].contained_symbols)
      llvm::errs() << ar->name << ";";
    llvm::errs() << "]\n";

    ++i;
    (*it)->dump();
  }
}

class ExprReplaceVisitor : public ExprVisitor {
private:
  ref<Expr> src, dst;

public:
  ExprReplaceVisitor(ref<Expr> _src, ref<Expr> _dst) : src(_src), dst(_dst) {}

  Action visitExpr(const Expr &e) {
    if (e == *src.get()) {
      return Action::changeTo(dst);
    } else {
      return Action::doChildren();
    }
  }

  Action visitExprPost(const Expr &e) {
    if (e == *src.get()) {
      return Action::changeTo(dst);
    } else {
      return Action::doChildren();
    }
  }
};

class ExprReplaceVisitor2 : public ExprVisitor {
private:
  const std::map<ref<Expr>, ref<Expr> > &replacements;

public:
  ExprReplaceVisitor2(const std::map<ref<Expr>, ref<Expr> > &_replacements)
      : ExprVisitor(true), replacements(_replacements) {}

  Action visitExprPost(const Expr &e) {
    std::map<ref<Expr>, ref<Expr> >::const_iterator it =
        replacements.find(ref<Expr>(const_cast<Expr *>(&e)));
    if (it != replacements.end()) {
      return Action::changeTo(it->second);
    } else {
      return Action::doChildren();
    }
  }
};

class ExprCountVisitor : public ExprVisitor {
private:
  uint64_t counter;

protected:
  Action visitRead(const ReadExpr &re) {
    const UpdateList &ul = re.updates;

    // XXX should we memo better than what ExprVisitor is doing for us?
    for (const UpdateNode *un=ul.head; un; un=un->next) {
      visit(un->index);
      visit(un->value);
    }

    if (ul.root->isSymbolicArray()) {
      auto pos = std::lower_bound(found_symbols.begin(), found_symbols.end(), ul.root);
      if (pos == found_symbols.end() || ul.root < *pos)
        found_symbols.insert(pos, ul.root);
    }

    return Action::doChildren();
  }

  Action visitExprPost(const Expr &e) {
    ++counter;
    return Action::skipChildren();
  }

public:
  std::vector<const Array*> found_symbols;

  ExprCountVisitor()
      : ExprVisitor(true), counter(0) {}

  uint64_t getCounter() {
    return counter;
  }

};

std::vector<const Array*> ConstraintSetView::getUsedArrays() const {
  std::vector<const Array*> usedArrays;

  for (auto o_pos: origPosition) {
    for (auto sym: o_pos.contained_symbols) {
      auto pos = std::lower_bound(usedArrays.begin(), usedArrays.end(), sym);
      if (pos == usedArrays.end() ||sym < *pos)
        usedArrays.insert(pos, sym);
    }
  }

  return usedArrays;
}

ConstraintPosition::ConstraintPosition(uint64_t constraint_id_, uint64_t constraint_width_,
    std::vector<const Array*> && contained_symbols_):
  constraint_id(constraint_id_), constraint_width(constraint_width_),
  contained_symbols(std::move(contained_symbols_)){}


//bool ConstraintPosition::operator==(const ConstraintPosition &pos) const {
//  // XXX CHECK
//  return (constraint_id == pos.constraint_id &&
//      (constraint_width == pos.constraint_width || constraint_width == 0));
//}

bool ConstraintManager::rewriteConstraints(ExprVisitor &visitor) {
  ConstraintSetView old;
  bool changed = false;

  constraintSetView.extractAndResetConstraints(old);
  for (ConstraintSetView::iterator it = old.constraints.begin(),
                                   ie = old.constraints.end();
       it != ie; ++it) {
    ref<Expr> &ce = *it;
    ref<Expr> e = visitor.visit(ce);

    auto positions = old.getPositions(it);

    if (e != ce) {
      ExprCountVisitor oldCountingVisitor;
      oldCountingVisitor.visit(ce);

      ExprCountVisitor newCountingVisitor;
      newCountingVisitor.visit(e);

      // enable further reductions
      addConstraintInternal(e, ConstraintPosition(positions.constraint_id,
          constraintSetView.version_cntr++,
          std::move(newCountingVisitor.found_symbols)));
      changed = true;
    } else {
      constraintSetView.push_back(ce, std::move(positions));
    }
  }

  return changed;
}

ref<Expr> ConstraintManager::simplifyExpr(ref<Expr> e,
                                          const ConstraintSetView &view) {
  if (isa<ConstantExpr>(e))
    return e;

  std::map<ref<Expr>, ref<Expr> > equalities;

  for (ConstraintSetView::constraints_ty::const_iterator
           it = view.constraints.begin(),
           ie = view.constraints.end();
       it != ie; ++it) {
    if (const EqExpr *ee = dyn_cast<EqExpr>(*it))
      if (isa<ConstantExpr>(ee->left)) {
        equalities.insert(std::make_pair(ee->right, ee->left));
        continue;
    }
    equalities.insert(std::make_pair(*it, ConstantExpr::alloc(1, Expr::Bool)));
  }

  return ExprReplaceVisitor2(equalities).visit(e);
}

ref<Expr> ConstraintManager::simplifyExpr(ref<Expr> e) {
  return ConstraintManager::simplifyExpr(e, constraintSetView);
}

void ConstraintManager::addConstraintInternal(ref<Expr> e,
                                              ConstraintPosition &&position) {
  // rewrite any known equalities and split Ands into different conjuncts
  switch (e->getKind()) {
  case Expr::Constant:
    assert(cast<ConstantExpr>(e)->isTrue() &&
           "attempt to add invalid (false) constraint");
//    constraintSetView.deletedPositions.insert(position);
    break;

  // split to enable finer grained independence and other optimizations
  case Expr::And: {
    BinaryExpr *be = cast<BinaryExpr>(e);

    // Find out the post-order number of the left expression,
    // which is the number of expressions in the left tree
    ExprCountVisitor leftTreeCountingVisitor;
    leftTreeCountingVisitor.visit(be->left);
    uint64_t left_node_count = leftTreeCountingVisitor.getCounter();

    ExprCountVisitor rightTreeCountingVisitor;
    rightTreeCountingVisitor.visit(be->right);

    // Using the node of the left tree and the whole tree,
    // we can calculate the absolute number
    uint64_t left_id =
        position.constraint_id - position.constraint_width + left_node_count;
    uint64_t right_id = position.constraint_id - 1;
    addConstraintInternal(
        be->left,
        ConstraintPosition(left_id, left_node_count,
                           std::move(leftTreeCountingVisitor.found_symbols)));
    addConstraintInternal(
        be->right, ConstraintPosition(
                       right_id, position.constraint_width - left_node_count,
                       std::move(rightTreeCountingVisitor.found_symbols)));
    break;
  }

  case Expr::Eq: {
    if (RewriteEqualities) {
      // XXX: should profile the effects of this and the overhead.
      // traversing the constraints looking for equalities is hardly the
      // slowest thing we do, but it is probably nicer to have a
      // ConstraintSet ADT which efficiently remembers obvious patterns
      // (byte-constant comparison).
      BinaryExpr *be = cast<BinaryExpr>(e);
      if (isa<ConstantExpr>(be->left)) {
        ExprReplaceVisitor visitor(be->right, be->left);
        rewriteConstraints(visitor);
      }
    }
    // update the number of queries

    constraintSetView.push_back(e, std::move(position));
    break;
  }

  default:
    constraintSetView.push_back(e, std::move(position));
    break;
  }
}

ConstraintPosition ConstraintSetView::getPositions(const_iterator it) const {
  return origPosition[it - constraints.begin()];
}

void ConstraintSetView::push_back(ref<Expr> e, ConstraintPosition &&positions) {
  constraints.push_back(e);
  origPosition.push_back(std::move(positions));
}

void ConstraintManager::addConstraint(ref<Expr> e) {
  TimerStatIncrementer t(stats::addConstraintTime);

  // simplify expression using existing constraints
  e = simplifyExpr(e);

  // count numbers of expression in simplified expression
  ExprCountVisitor countingVisitor;
  countingVisitor.visit(e);
  uint64_t count_nodes = countingVisitor.getCounter();

  // assign the new space
  ConstraintSetView::next_free_position += count_nodes;
  uint64_t expression_position = ConstraintSetView::next_free_position;
//  llvm::errs() << "Before: ";
//  for (auto i: constraintSetView.origPosition)
//	  llvm::errs() << i.constraint_id << ":" << i.constraint_width << ", ";

  addConstraintInternal(
      e, ConstraintPosition(expression_position, count_nodes,
                            std::move(countingVisitor.found_symbols)));
//
//  llvm::errs() << "After: ";
//  for (auto i: constraintSetView.origPosition)
//	  llvm::errs() << i.constraint_id << ":" << i.constraint_width << ", ";
  // shuffle constraints such that they are ordered by origPosition
  auto it = std::is_sorted_until(constraintSetView.origPosition.begin(),
                                 constraintSetView.origPosition.end(), ConstraintPositionLess());

  while (it != constraintSetView.origPosition.end()) {
    auto new_pos = std::lower_bound(constraintSetView.origPosition.begin(), it,
                                    *it, ConstraintPositionLess());

    auto idx_old = it - constraintSetView.origPosition.begin();
    auto idx_new = new_pos - constraintSetView.origPosition.begin();

//    llvm::errs() << "POS " << it->constraint_id << " " << idx_new << "\n";
//    llvm::errs() << "IDX " << idx_old << " " << idx_new << "\n";
    constraintSetView.origPosition.insert(new_pos, *it);
    constraintSetView.origPosition.erase(
        constraintSetView.origPosition.begin() + idx_old + 1);

    constraintSetView.constraints.insert(
        constraintSetView.constraints.begin() + idx_new,
        constraintSetView.constraints[idx_old]);
    constraintSetView.constraints.erase(constraintSetView.constraints.begin() +
                                        idx_old + 1);

    // continue checking the remaining array
    it = std::is_sorted_until(constraintSetView.origPosition.begin() + idx_new,
                              constraintSetView.origPosition.end(), ConstraintPositionLess());
  }
}

void SimpleConstraintManager::push_back(ref<Expr> expr) {
  // We explicitly initialize the constraint position to 0
  // this should not be used to track constraints
  constraintSetView.push_back(expr,
      ConstraintPosition(0, 0, std::vector<const Array*>()));
}

void ReferencingConstraintManager::push_back(ref<Expr> expr) {
    auto it = std::find(oldView.begin(), oldView.end(), expr);
    if (it == oldView.end()) {
      // count numbers of expression in simplified expression
      ExprCountVisitor countingVisitor;
      countingVisitor.visit(expr);
      constraintSetView.push_back(expr, ConstraintPosition(/* unknown */ 0, /* unknown */ 0, std::move(countingVisitor.found_symbols)));
    } else
      constraintSetView.push_back(expr, oldView.getPositions(it));
  }

void SimpleConstraintManager::clear() {
   constraintSetView.constraints.clear();
   constraintSetView.origPosition.clear();
//    constraintSetView.next_free_position = 0;
 }
