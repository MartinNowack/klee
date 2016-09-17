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
  std::swap(trackPos, other.trackPos);
  //  deletedPositions.swap(other.deletedPositions);
  //  std::swap(uid_cntr, other.uid_cntr);
  //  std::swap(next_free_position, other.next_free_position);
}

ConstraintSetView ConstraintSetView::clone() const {
  return ConstraintSetView(*this);
}

ConstraintSetView::ConstraintSetView() : trackPos(false) {}

ConstraintSetView::ConstraintSetView(const ConstraintSetView &csv) {
  constraints.reserve(csv.constraints.size());
  for (auto cs : csv.constraints)
    constraints.emplace_back(cs);
  trackPos = csv.trackPos;
  origPosition.reserve(csv.origPosition.size());
  for (auto pos : csv.origPosition)
    origPosition.emplace_back(pos);
  //    for(auto elem: csv.independence_cache)
  //     independence_cache.insert(std::make_pair(std::make_uniqe_ptr));
}

bool ConstraintSetView::operator==(const ConstraintSetView &other) const {
  return constraints == other.constraints;
}

void ConstraintSetView::dump() const {
  size_t i = 0;
  for (const_iterator it = constraints.begin(), itE = constraints.end();
       it != itE; ++it) {
    llvm::errs() << "{" << origPosition[i].constraint_id << "/"
                 << origPosition[i].constraint_width << "}\n";
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
  Action visitExprPost(const Expr &e) {
    ++counter;
    return Action::skipChildren();
  }

public:
  ExprCountVisitor() : ExprVisitor(true), counter(0) {}

  uint64_t getCounter() { return counter; }
};

ConstraintPosition::ConstraintPosition(
    uint64_t constraint_id_, uint64_t constraint_width_, uint64_t version_)
    : constraint_id(constraint_id_), constraint_width(constraint_width_),
      version(version_) {}

void ConstraintPosition::dump() const {
  llvm::errs() << "(" << constraint_id << ":" << constraint_width << ")\n";
}

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
      // enable further reductions
      addConstraintInternal(
          e, ConstraintPosition(positions.constraint_id,
                                positions.constraint_width,
                                constraintSetView.version_cntr++));
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

    // Using the node of the left tree and the whole tree,
    // we can calculate the absolute number
    uint64_t left_id =
        position.constraint_id - position.constraint_width + left_node_count;
    uint64_t right_id = position.constraint_id - 1;
    addConstraintInternal(
        be->left,
        ConstraintPosition(left_id, left_node_count, position.version));
    addConstraintInternal(
        be->right, ConstraintPosition(
                       right_id, position.constraint_width - left_node_count,
                       position.version));
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
  assert(trackPos || constraints.empty());
  return origPosition[it - constraints.begin()];
}

ConstraintPosition ConstraintSetView::getPositions(size_t pos) const {
  assert(trackPos || constraints.empty());
  return origPosition[pos];
}

void ConstraintSetView::push_back(ref<Expr> e, ConstraintPosition &&positions) {
  assert(trackPos || constraints.empty());
  trackPos = true;
  constraints.push_back(e);
  origPosition.push_back(std::move(positions));
}

void ConstraintSetView::push_nontracking(ref<Expr> e) {
  assert(!trackPos || origPosition.empty());
  trackPos = false;
  constraints.push_back(e);
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

  addConstraintInternal(
      e, ConstraintPosition(expression_position, count_nodes, 0));

  // Sort constraints by origPosition
  auto it = std::is_sorted_until(constraintSetView.origPosition.begin(),
                                 constraintSetView.origPosition.end(),
                                 ConstraintPositionLess());

  while (it != constraintSetView.origPosition.end()) {
    auto new_pos = std::lower_bound(constraintSetView.origPosition.begin(), it,
                                    *it, ConstraintPositionLess());

    auto idx_old = it - constraintSetView.origPosition.begin();
    auto idx_new = new_pos - constraintSetView.origPosition.begin();

    std::rotate(new_pos, it, it + 1);
    std::rotate(constraintSetView.constraints.begin() + idx_new,
                constraintSetView.constraints.begin() + idx_old,
                constraintSetView.constraints.begin() + idx_old + 1);

    // continue checking the remaining array
    it = std::is_sorted_until(constraintSetView.origPosition.begin() + idx_new,
                              constraintSetView.origPosition.end(),
                              ConstraintPositionLess());
  }
}

void SimpleConstraintManager::push_back(ref<Expr> expr) {
  // We explicitly initialize the constraint position to 0
  // this should not be used to track constraints
  constraintSetView.push_back(expr, ConstraintPosition(0, 0, 0));
}

void SimpleConstraintManager::push_back_nontracking(ref<Expr> expr) {
  // We explicitly initialize the constraint position to 0
  // this should not be used to track constraints
  constraintSetView.push_nontracking(expr);
}

void ReferencingConstraintManager::push_back(ref<Expr> expr) {
  const Expr *p = expr.get();
  size_t pos = 0;
  for (const auto &e : oldView.constraints) {
    if (e.get() == p) {
      constraintSetView.push_back(expr, oldView.getPositions(pos));
      return;
    }
    ++pos;
  }
  assert(0 && "Expression to be add not found in previous one");
}

void SimpleConstraintManager::clear() {
  constraintSetView.constraints.clear();
  constraintSetView.origPosition.clear();
  //    constraintSetView.next_free_position = 0;
}
