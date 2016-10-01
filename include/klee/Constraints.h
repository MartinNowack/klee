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

#include <cstddef>
#include <cstdint>
#include <iterator>
#include <type_traits>
#include <unordered_map>
#include <vector>

#include "klee/Expr.h"
#include "klee/util/IndependentElementSet.h"
#include "klee/util/Ref.h"

namespace klee {

class Array;
class ConstraintManager;
class ConstraintSetView;
class Expr;
class ExprVisitor;
class ReferencingConstraintManager;
class SimpleConstraintManager;

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

template <bool> class ConstraintSetIterator;

/**
 * @brief Container to keep all constraints
 */
class ConstraintSetView {
public:
  typedef ConstraintSetIterator<false> iterator;
  typedef ConstraintSetIterator<true> const_iterator;

  bool empty() const;
  iterator begin() const;
  iterator end() const;
  size_t size() const;

  iterator begin(ref<Expr> &e) const;
  iterator end(ref<Expr> &e) const;

  std::vector<IndependentElementSet>::iterator iset_begin() const {
    return independence_cache.begin();
  }
  std::vector<IndependentElementSet>::iterator iset_end() const {
    return independence_cache.end();
  }

  ConstraintPosition getPositions(const const_iterator &it) const;

  bool operator==(const ConstraintSetView &other) const;

  void dump() const;

  // XXX private?
  ConstraintSetView();
  ConstraintSetView &operator=(const ConstraintSetView &) = delete;

  ConstraintSetView(ConstraintSetView &&) = default;
  ConstraintSetView &operator=(ConstraintSetView &&) = default;

  ConstraintSetView clone() const;
  // XXX create referencing set view instead
  ConstraintSetView filterClone(const ref<Expr> &) const;

private:
  ConstraintSetView(const ConstraintSetView &csv);

  void push_back(ref<Expr> e, ConstraintPosition &&positions);
  void addExprAndUpdateIndependentSet(ref<Expr> e,
                                      ConstraintPosition &&positions);

  void clear();

  /**
   * Moves constraints to other but keeps state.
   */
  void extractAndResetConstraints(ConstraintSetView &other);

  /**
   * Moves constraints from other view, which do not intersect with
   * constraints from this set.
   *
   */
  void addNoneIntersectionExpressions(ConstraintSetView &other);

  void orderIndependenceSetByConstraintPosition();
  static uint64_t next_free_position;
  static uint64_t version_cntr;

public:
  // Tracks origin position for each constraint for each independence set
  std::vector<std::vector<ConstraintPosition> > origPosition;

  // Track independence sets
  // Sets are disjunct
  mutable std::vector<IndependentElementSet> independence_cache;

  friend ConstraintManager;
  friend SimpleConstraintManager;
  friend ReferencingConstraintManager;
  friend ConstraintSetIterator<true>;
  friend ConstraintSetIterator<false>;
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
  bool rewriteConstraints(ExprVisitor &visitor, ref<Expr> e);

  void addConstraintInternal(ref<Expr> e, ConstraintPosition &&position);
};

/**
 * @brief Iterator class to iterate over constraints of a constraint set
 */
template <bool is_constant> class ConstraintSetIterator {
public:
  typedef std::forward_iterator_tag iterator_category;
  typedef typename std::conditional<is_constant, const ref<Expr>,
                                    ref<Expr> >::type value_type;
  typedef ptrdiff_t difference_type;
  typedef typename std::conditional<is_constant, const ref<Expr> *,
                                    ref<Expr> *>::type pointer;
  typedef typename std::conditional<is_constant, const ref<Expr> &,
                                    ref<Expr> &>::type reference;

  ConstraintSetIterator(const ConstraintSetView *csv_, size_t iset_idx_,
                        size_t iset_expr_idx_)
      : csv(csv_), iset_idx(iset_idx_), iset_expr_idx(iset_expr_idx_),
        e(nullptr) {
    // set to the number entries of independence sets we have
    iset_idx_max = csv->independence_cache.size();

    // Update the max number of entries in the selected independence set
    // if it exists
    if (iset_idx < iset_idx_max)
      iset_expr_idx_max = csv->independence_cache[iset_idx].exprs.size();
    else
      iset_expr_idx_max = 0;
  }

  ConstraintSetIterator(const ConstraintSetView *csv_, size_t iset_idx_,
                        size_t iset_expr_idx_, ref<Expr> ex)
      : csv(csv_), iset_idx(iset_idx_), iset_expr_idx(iset_expr_idx_), e(ex) {
    currentIndepSet.add(IndependentElementSet(ex));
    iset_idx_max = csv->independence_cache.size();

    // search for a independent set which matches
    for (; iset_idx < iset_idx_max; ++iset_idx)
      if (currentIndepSet.intersects(csv->independence_cache[iset_idx]))
        break;

    // Update the max number of entries in the selected independence set
    // if it exists
    if (iset_idx < iset_idx_max)
      iset_expr_idx_max = csv->independence_cache[iset_idx].exprs.size();
    else
      iset_expr_idx_max = 0;
  }

  /**
   * Copy constructor. Allows for implicit conversion from a regular iterator to
   * a const_iterator
   */
  ConstraintSetIterator(const ConstraintSetIterator<false> &other)
      : csv(other.csv), currentIndepSet(other.currentIndepSet.clone()),
        iset_idx(other.iset_idx), iset_expr_idx(other.iset_expr_idx),
        iset_idx_max(other.iset_idx_max), iset_expr_idx_max(other.iset_expr_idx_max),
        e(other.e){}

  bool operator!=(const ConstraintSetIterator &other) const {
    return (iset_idx != other.iset_idx || iset_expr_idx != other.iset_expr_idx);
  }

  reference operator*() const {
    assert(iset_idx < iset_idx_max);
    assert(iset_expr_idx < iset_expr_idx_max);

    return csv->independence_cache[iset_idx].exprs[iset_expr_idx];
  }

  ConstraintSetIterator &operator++() {
    ++iset_expr_idx;
    // check if the end of this set is reached, and the next one has to be
    // selected
    if (iset_expr_idx >= iset_expr_idx_max) {
      // jump to the next independence cache item
      // and start from the beginning
      iset_expr_idx = 0;
      if (!e.isNull()) {
        ++iset_idx;
        // search for a independent set which matches the given expression
        for (; iset_idx < iset_idx_max; ++iset_idx)
          if (currentIndepSet.intersects(csv->independence_cache[iset_idx]))
            break;
      } else
        ++iset_idx;
      // update the max counter fpr expressions of the next indepencence set
      if (iset_idx < iset_idx_max)
        iset_expr_idx_max = csv->independence_cache[iset_idx].exprs.size();
      else
        iset_expr_idx_max = 0;
    }
    return *this;
  }

  ConstraintSetIterator operator++(int) {
    // Use operator++()
    const ConstraintSetIterator old(*this);
    ++(*this);
    return old;
  }

private:
  const ConstraintSetView *csv;
  IndependentElementSet currentIndepSet;

  size_t iset_idx;
  size_t iset_expr_idx;

  size_t iset_idx_max;
  size_t iset_expr_idx_max;

  ref<Expr> e;

  friend ConstraintSetView;
  friend class ConstraintSetIterator<true>;
};
/**
 * Can add constraints without position tracking
 */
class SimpleConstraintManager : public ConstraintManager {
public:
  SimpleConstraintManager(ConstraintSetView &view) : ConstraintManager(view) {}

  // Add constraint without simplification
  void push_back(ref<Expr> expr);

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
