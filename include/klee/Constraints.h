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

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "Expr.h"
#include "klee/util/IndependentElementSet.h"
#include "util/Ref.h"

namespace klee {

class Array;
class ConstraintManager;
class ConstraintSetView;
class Expr;
class ExprVisitor;
class ReferencingConstraintManager;
class SimpleConstraintManager;
class IndependentElementSet;

struct ConstraintPosition {
  // Unique ID of the constraint
  uint64_t constraint_id;

  // Width of the constraint, which is essentially the
  // number of nodes
  uint64_t constraint_width;

  // Version of constraint position
  uint64_t version;

  ConstraintPosition(uint64_t constraint_id_, uint64_t constraint_width_,
                     uint64_t version);
  void dump() const;
};
}

struct ConstraintPositionHash {
  size_t operator()(const klee::ConstraintPosition &e) const {
    return std::hash<uint64_t>()(e.constraint_id);
  }
};

struct ConstraintPositionEqual {
  bool operator()(const klee::ConstraintPosition &a,
                  const klee::ConstraintPosition &b) const {
    if (a.constraint_id != b.constraint_id)
      return false;
    if (a.constraint_width != b.constraint_width)
      return false;
    return true;
  }
};

struct ConstraintPositionLess {
  bool operator()(const klee::ConstraintPosition &a,
                  const klee::ConstraintPosition &b) const {
    if (a.constraint_id < b.constraint_id)
      return true;
    if (a.constraint_id == b.constraint_id &&
        a.constraint_width < b.constraint_width)
      return false;
    return true;
  }
};

namespace klee {
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
  constraint_iterator begin() const { return constraints.cbegin(); }
  constraint_iterator end() const { return constraints.cend(); }
  size_t size() const { return constraints.size(); }

  ConstraintSetView():trackPos(false) {}

public:
  ConstraintSetView &operator=(const ConstraintSetView &) = delete;

  ConstraintSetView(ConstraintSetView &&) = default;
  ConstraintSetView &operator=(ConstraintSetView &&) = default;

  bool operator==(const ConstraintSetView &other) const;

  void dump() const;

  ConstraintSetView clone() const { return ConstraintSetView(*this); }

private:
  ConstraintSetView(const ConstraintSetView &csv) {
    constraints.reserve(csv.constraints.size());
    for (auto cs : csv.constraints)
      constraints.emplace_back(cs);
    trackPos = csv.trackPos;
    origPosition.reserve(csv.origPosition.size());
    for (auto pos : csv.origPosition)
      origPosition.emplace_back(pos);
    //    for(auto elem: csv.independence_cache)
    //	   independence_cache.insert(std::make_pair(std::make_uniqe_ptr));
  }

  void push_back(ref<Expr> e, ConstraintPosition &&positions);
  void push_nontracking(ref<Expr> e);

  /**
   * Moves constraints to other but keeps state.
   */
  void extractAndResetConstraints(ConstraintSetView &other);

public:
  constraints_ty constraints;

private:
  static uint64_t next_free_position;
  static uint64_t version_cntr;

  // Tracks origin position for each set
  // First: the origin position, second unique id
  std::vector<ConstraintPosition> origPosition;

  // Indicator if positions are tracked by this view or not
  bool trackPos;

  // Track independence sets
  std::vector<std::pair<std::unique_ptr<IndependentElementSet>,
                        std::vector<ref<Expr> > > >
      independence_cache;

public:
  ConstraintPosition getPositions(const_iterator it) const;
  ConstraintPosition getPositions(size_t pos) const;
};

/**
 * Class to manipulate Constraint containers
 */
class ConstraintManager {
public:
  // create from constraints with no optimization
  explicit ConstraintManager(ConstraintSetView &set) : constraintSetView(set) {}

  static ref<Expr> simplifyExpr(ref<Expr> e, const ConstraintSetView &view);

  ref<Expr> simplifyExpr(ref<Expr> e);

  void addConstraint(ref<Expr> e);

  bool operator==(const ConstraintManager &other) const {
    return constraintSetView == other.constraintSetView;
  }

  ConstraintManager(const ConstraintManager &) = delete;
  ConstraintManager &operator=(const ConstraintManager &) = delete;

protected:
  ConstraintSetView &constraintSetView;
  // returns true iff the constraints were modified
  bool rewriteConstraints(ExprVisitor &visitor);

  void addConstraintInternal(ref<Expr> e, ConstraintPosition &&position);
};

/**
 * Can add constraints without position tracking
 */
class SimpleConstraintManager : public ConstraintManager {
public:
  SimpleConstraintManager(ConstraintSetView &view) : ConstraintManager(view) {}

  // Add constraint without simplification
  void push_back(ref<Expr> expr);
  void push_back_nontracking(ref<Expr> expr);

  SimpleConstraintManager(const SimpleConstraintManager &) = delete;

  void clear();
};

/**
 * Add constraints keeping track of the origin constructs
 */
class ReferencingConstraintManager : public ConstraintManager {
public:
  ReferencingConstraintManager(ConstraintSetView &newView,
                               const ConstraintSetView &_oldView)
      : ConstraintManager(newView), oldView(_oldView) {}
  void push_back(ref<Expr> expr);

  ReferencingConstraintManager(const SimpleConstraintManager &) = delete;

private:
  const ConstraintSetView &oldView;
};
}

#endif /* KLEE_CONSTRAINTS_H */
