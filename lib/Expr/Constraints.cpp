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
#include <iterator>
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
  independence_cache.swap(other.independence_cache);
  origPosition.swap(other.origPosition);
}

void ConstraintSetView::addNoneIntersectionExpressions(ConstraintSetView &other) {
  // check if we can copy all
  if (independence_cache.empty()) {
    independence_cache = std::move(other.independence_cache);
    origPosition = std::move(other.origPosition);
    return;
  }
  // Analyze which independence sets do not interleave
  std::vector<size_t> indices;
  for (size_t i = 0, e = other.independence_cache.size(); i != e; ++i) {
    for (auto & item:independence_cache){
      if (!item.intersects(other.independence_cache[i]))
        indices.push_back(i);
    }
  }

  // Now, move those set to this set
  for (auto index: indices){
    independence_cache.push_back(std::move(other.independence_cache[index]));
    origPosition.push_back(std::move(other.origPosition[index]));
  }
}


ConstraintSetView ConstraintSetView::clone() const {
  return ConstraintSetView(*this);
}
ConstraintSetView ConstraintSetView::filterClone(const ref<Expr> &e) const {
  IndependentElementSet es(e);
  ConstraintSetView result;

  for (size_t i = 0, j = independence_cache.size(); i < j; ++i) {
    if (!independence_cache[i].intersects(es))
      continue;
    result.independence_cache.push_back(independence_cache[i].clone());
    result.origPosition.push_back(origPosition[i]);
  }
  return result;
}

ConstraintSetView::ConstraintSetView() {}

bool ConstraintSetView::operator==(const ConstraintSetView &other) const {
  return independence_cache == other.independence_cache;
}

void ConstraintSetView::dump() const {
  for (auto it = begin(), itE = end(); it != itE; ++it) {
    auto origPosition = getPositions(it);
    llvm::errs() << "{" << origPosition.constraint_id << "/"
                 << origPosition.constraint_width << "}\n";
    (*it)->dump();
  }
}

inline void ConstraintSetView::orderIndependenceSetByConstraintPosition() {
  // Sort constraints by origPosition
  for (size_t i = 0, j = independence_cache.size(); i < j; ++i) {
    auto it =
        std::is_sorted_until(origPosition[i].begin(), origPosition[i].end(),
                             ConstraintPositionLess());

    while (it != origPosition[i].end()) {
      auto new_pos = std::lower_bound(origPosition[i].begin(), it, *it,
                                      ConstraintPositionLess());

      auto idx_old = it - origPosition[i].begin();
      auto idx_new = new_pos - origPosition[i].begin();

      std::rotate(new_pos, it, it + 1);
      std::rotate(independence_cache[i].exprs.begin() + idx_new,
                  independence_cache[i].exprs.begin() + idx_old,
                  independence_cache[i].exprs.begin() + idx_old + 1);

      // continue checking the remaining array
      it =
          std::is_sorted_until(origPosition[i].begin() + idx_new,
                               origPosition[i].end(), ConstraintPositionLess());
    }
  }
}

inline ConstraintSetView::ConstraintSetView(const ConstraintSetView &csv)
    : origPosition(csv.origPosition) {
  independence_cache.reserve(csv.independence_cache.size());
  std::for_each(csv.independence_cache.begin(), csv.independence_cache.end(),
                [=](IndependentElementSet &ies) {
    independence_cache.push_back(ies.clone());
  });
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

bool ConstraintManager::rewriteConstraints(ExprVisitor &visitor, ref<Expr> e_) {
  ConstraintSetView old;
  bool changed = false;

  constraintSetView.extractAndResetConstraints(old);
  IndependentElementSet is(e_);
  size_t index = 0;
  std::vector<size_t> to_copy;
  for (auto iset_it = old.iset_begin(), iset_itE = old.iset_end();
       iset_it != iset_itE; ++iset_it, ++index) {
    if (!is.intersects(*iset_it)) {
      to_copy.push_back(index);
      continue;
    }
    size_t expr_idx = 0;
    for (auto it = iset_it->exprs.begin(), ie = iset_it->exprs.end(); it != ie;
         ++it, ++expr_idx) {
      ref<Expr> &ce = *it;
      ref<Expr> e = visitor.visit(ce);

      auto positions = old.origPosition[index][expr_idx];
      if (e != ce) {
        // enable further reductions
        addConstraintInternal(
            e, ConstraintPosition(positions.constraint_id,
                                  positions.constraint_width,
                                  constraintSetView.version_cntr++));
        changed = true;
      } else {
        constraintSetView.push_back(ce, ConstraintPosition(positions));
      }
    }
  }

  // check if we can copy all
  if (constraintSetView.independence_cache.empty() && !changed) {
    constraintSetView.independence_cache = std::move(old.independence_cache);
    constraintSetView.origPosition = std::move(old.origPosition);

    return changed;
  }
  while (!to_copy.empty()) {
    auto index = to_copy.back();
    to_copy.pop_back();
    constraintSetView.independence_cache.push_back(
        std::move(old.independence_cache[index]));
    constraintSetView.origPosition.push_back(
        std::move(old.origPosition[index]));
  }

  return changed;
}

bool ConstraintSetView::empty() const { return independence_cache.empty(); }

ConstraintSetView::iterator ConstraintSetView::begin() const {
  return ConstraintSetView::iterator(this, 0, 0);
}
ConstraintSetView::iterator ConstraintSetView::end() const {
  return ConstraintSetView::iterator(this, this->independence_cache.size(), 0);
}

ConstraintSetView::iterator ConstraintSetView::begin(ref<Expr> &e) const {
  return ConstraintSetView::iterator(this, 0, 0, e);
}

ConstraintSetView::iterator ConstraintSetView::end(ref<Expr> &e) const {
  return ConstraintSetView::iterator(this, this->independence_cache.size(), 0,
                                     e);
}

void ConstraintSetView::addExprAndUpdateIndependentSet(
    ref<Expr> e, ConstraintPosition &&positions) {
  // check every view
  IndependentElementSet new_set(e);
  std::vector<size_t> possibleSets;
  size_t idx = 0;
  for (auto &other_set : independence_cache) {
    if (other_set.intersects(new_set)) {
      possibleSets.push_back(idx);
    }
    ++idx;
  }
  // We could not add the constraint to an existing set
  // Add it as a new set
  if (possibleSets.empty()) {
    independence_cache.emplace_back(std::move(new_set));
    origPosition.emplace_back(std::vector<ConstraintPosition>());
    origPosition.back().emplace_back(positions);
    return;
  }

  std::vector<ConstraintPosition> new_positions;
  new_positions.emplace_back(positions);

  // The constraint is dependent on one or more sets
  // merge those sets to one big set
  while (possibleSets.size() > 1) {
    size_t current_idx = possibleSets.back();
    possibleSets.pop_back();
    new_set.add(independence_cache[current_idx]);
    independence_cache.erase(independence_cache.begin() + current_idx);
    // Save positions
    new_positions.insert(
        new_positions.end(),
        std::make_move_iterator(origPosition[current_idx].begin()),
        std::make_move_iterator(origPosition[current_idx].end()));
    origPosition.erase(origPosition.begin() + current_idx);
  }
  independence_cache[possibleSets[0]].add(new_set);
  origPosition[possibleSets[0]].insert(
      origPosition[possibleSets[0]].end(),
      std::make_move_iterator(new_positions.begin()),
      std::make_move_iterator(new_positions.end()));
}

ConstraintPosition ConstraintSetView::getPositions(
    const ConstraintSetView::const_iterator &it) const {
  return origPosition[it.iset_idx][it.iset_expr_idx];
}

void ConstraintSetView::clear() {
  independence_cache.clear();
  origPosition.clear();
}

void ConstraintSetView::push_back(ref<Expr> e, ConstraintPosition &&positions) {
  assert(!e.isNull());
  addExprAndUpdateIndependentSet(e, std::move(positions));
}

size_t ConstraintSetView::size() const {
  size_t total = 0;
  for (auto &cache_item : independence_cache)
    total += cache_item.exprs.size();
  return total;
}

////

ref<Expr> ConstraintManager::simplifyExpr(ref<Expr> e,
                                          const ConstraintSetView &view) {
  if (isa<ConstantExpr>(e))
    return e;

  // We can only simplify an expression by other constraints, if they have at
  // least one variable in common

  std::map<ref<Expr>, ref<Expr> > equalities;

  std::for_each(view.begin(e), view.end(e), [&equalities](ref<Expr> e) {
    if (const EqExpr *ee = dyn_cast<EqExpr>(e))
      if (isa<ConstantExpr>(ee->left)) {
        equalities.insert(std::make_pair(ee->right, ee->left));
        return;
      }
    equalities.insert(std::make_pair(e, ConstantExpr::alloc(1, Expr::Bool)));
  });

  return ExprReplaceVisitor2(equalities).visit(e);
}

ref<Expr> ConstraintManager::simplifyExpr(ref<Expr> e) {
  return ConstraintManager::simplifyExpr(e, constraintSetView);
}

void ConstraintManager::addConstraintInternal(ref<Expr> new_constraint,
                                              ConstraintPosition &&new_position) {

  std::vector<std::pair<ref<Expr>, ConstraintPosition> > working_stack;
  working_stack.push_back(std::make_pair(new_constraint, new_position));

  ref<Expr> currentItem;
  while(!working_stack.empty()) {
    auto w = working_stack.back();
    working_stack.pop_back();
    currentItem = w.first;
    auto position = w.second;

    // rewrite any known equalities and split Ands into different conjuncts
    switch (currentItem->getKind()) {
    case Expr::Constant:
      assert(cast<ConstantExpr>(currentItem)->isTrue() &&
             "attempt to add invalid (false) constraint");
      //    constraintSetView.deletedPositions.insert(position);
      break;

    // split to enable finer grained independence and other optimizations
    case Expr::And: {
      BinaryExpr *be = cast<BinaryExpr>(currentItem);

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

      working_stack.push_back(std::make_pair(be->left,
          ConstraintPosition(left_id, left_node_count, position.version)));
      working_stack.push_back(std::make_pair(be->right,
          ConstraintPosition(right_id, position.constraint_width - left_node_count,
          position.version)));

      break;
    }

    case Expr::Eq: {
      if (RewriteEqualities) {
        // XXX: should profile the effects of this and the overhead.
        // traversing the constraints looking for equalities is hardly the
        // slowest thing we do, but it is probably nicer to have a
        // ConstraintSet ADT which efficiently remembers obvious patterns
        // (byte-constant comparison).
        BinaryExpr *be = cast<BinaryExpr>(currentItem);
        if (isa<ConstantExpr>(be->left)) {
          ExprReplaceVisitor visitor(be->right, be->left);
          rewriteConstraints(visitor, be->right);
        }
      }
      // update the number of queries
      constraintSetView.push_back(currentItem, std::move(position));
      break;
    }

    default:
      constraintSetView.push_back(currentItem, std::move(position));
      break;
    }
  }

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

  constraintSetView.orderIndependenceSetByConstraintPosition();
}

void SimpleConstraintManager::push_back(ref<Expr> expr) {
  // We explicitly initialize the constraint position to 0
  // this should not be used to track constraints
  constraintSetView.push_back(expr, ConstraintPosition(0, 0, 0));
}

void ReferencingConstraintManager::push_back(ref<Expr> expr) {

  auto it_pos = std::find(oldView.begin(expr), oldView.end(expr), expr);
  assert(it_pos != oldView.end(expr) && "Constraint was not added beforehand");

  constraintSetView.push_back(expr, oldView.getPositions(it_pos));
}

void SimpleConstraintManager::clear() { constraintSetView.clear(); }
