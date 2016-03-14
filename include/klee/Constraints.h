//===-- Constraints.h -------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_CONSTRAINTS_H
#define KLEE_CONSTRAINTS_H

#include <stddef.h>
#include <sys/types.h>
#include <algorithm>
#include <iterator>
#include <vector>
#include <unordered_set>

#include "util/Ref.h"

namespace klee {

class ExprVisitor;
class ConstraintManager;
class SimpleConstraintManager;
class ReferencingConstraintManager;
class Expr;

/**
 * @brief Container to keep all constraints
 */
class ConstraintSetView {
  friend ConstraintManager;
  friend SimpleConstraintManager;
  friend ReferencingConstraintManager;

public:
  typedef std::vector<ref<Expr> > constraints_ty;
  typedef std::vector<ref<Expr> >::const_iterator constraint_iterator;

  typedef constraints_ty::iterator iterator;
  typedef constraints_ty::const_iterator const_iterator;

  bool empty() const { return constraints.empty(); }
  constraint_iterator begin() const { return constraints.begin(); }
  constraint_iterator end() const { return constraints.end(); }
  size_t size() const { return constraints.size(); }

  ConstraintSetView() : next_free_position(0) {}

  bool operator==(const ConstraintSetView &other) const {
    return constraints == other.constraints;
  }
  void dump() const;

private:
  void push_back(ref<Expr> e, size_t positions) {
    constraints.push_back(e);
    origPosition.push_back(positions);
  }

  void swap(ConstraintSetView &other);
  constraints_ty constraints;
  int64_t next_free_position;

  // Tracks origin position for each set
  std::vector<int64_t> origPosition;
  std::unordered_set<int64_t> deletedPositions;

public:
  int64_t getPositions(const_iterator it) const {
    return origPosition[it - constraints.begin()];
  }

  bool isDeleted(int64_t pos) const { return deletedPositions.count(pos); }
};

/**
 * Class to manipulate Constraint containers
 */
class ConstraintManager {
public:
  // create from constraints with no optimization
  explicit ConstraintManager(ConstraintSetView &set) : constraintSetView(set) {}

  ConstraintManager(const ConstraintManager &cs)
      : constraintSetView(cs.constraintSetView) {}

  static ref<Expr> simplifyExpr(ref<Expr> e, const ConstraintSetView &view);

  ref<Expr> simplifyExpr(ref<Expr> e);

  void addConstraint(ref<Expr> e);

  bool operator==(const ConstraintManager &other) const {
    return constraintSetView == other.constraintSetView;
  }

  virtual ~ConstraintManager(){};

protected:
  ConstraintSetView &constraintSetView;
  // returns true iff the constraints were modified
  bool rewriteConstraints(ExprVisitor &visitor);

  void addConstraintInternal(ref<Expr> e, size_t position);
};

/**
 * Can add constraints without position tracking
 */
class SimpleConstraintManager : public ConstraintManager {
public:
  SimpleConstraintManager(ConstraintSetView &view) : ConstraintManager(view) {}
  // Add Constaint without simplification
  void push_back(ref<Expr> expr) {
    constraintSetView.push_back(expr, constraintSetView.next_free_position++);
  }

  SimpleConstraintManager(const SimpleConstraintManager &) = delete;

  void clear() {
    constraintSetView.constraints.clear();
    constraintSetView.origPosition.clear();
    constraintSetView.next_free_position = 0;
  }
};

/**
 * Add constraints keeping track of the origin constructs
 */
class ReferencingConstraintManager : public ConstraintManager {
public:
  ReferencingConstraintManager(ConstraintSetView &newView,
                               const ConstraintSetView &_oldView)
      : ConstraintManager(newView), oldView(_oldView) {}
  void push_back(ref<Expr> expr) {
    auto it = std::find(oldView.begin(), oldView.end(), expr);
    if (it == oldView.end())
      constraintSetView.push_back(expr, /* unknown */ -1);
    else
      constraintSetView.push_back(expr, oldView.getPositions(it));
  }

  ReferencingConstraintManager(const SimpleConstraintManager &) = delete;

private:
  const ConstraintSetView &oldView;
};
}

#endif /* KLEE_CONSTRAINTS_H */
