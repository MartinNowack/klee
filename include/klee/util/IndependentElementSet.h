//===-- IndependentSolver.cpp ---------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#ifndef KLEE_UTIL_INDEPENDENTELEMENTSET_H
#define KLEE_UTIL_INDEPENDENTELEMENTSET_H

#include "llvm/ADT/SparseBitVector.h"
#include <list>
#include <map>
#include <set>
#include <vector>

#include "klee/Expr.h"
#include "Ref.h"

namespace klee {
class ConstraintSetView;
struct Query;
} /* namespace klee */

namespace klee {

class IndependentElementSet {
public:
  typedef std::map<const Array *, llvm::SparseBitVector<64> > elements_ty;
  elements_ty
      elements; // Represents individual elements of array accesses (arr[1])
  std::set<const Array *>
      wholeObjects; // Represents symbolically accessed arrays (arr[x])
  std::vector<ref<Expr> >
      exprs; // All expressions that are associated with this factor
             // Although order doesn't matter, we use a vector to match
             // the ConstraintManager constructor that will eventually
             // be invoked.

  IndependentElementSet(){};
  explicit IndependentElementSet(ref<Expr> e);
  IndependentElementSet &operator=(const IndependentElementSet &ies) = delete;
  IndependentElementSet(IndependentElementSet &&set) = default;
  IndependentElementSet &operator=(IndependentElementSet &&set) = default;

  void print(llvm::raw_ostream &os) const;

  bool intersects(const IndependentElementSet &b) const;
  bool add(const IndependentElementSet &b);

  IndependentElementSet clone() const;
  bool operator==(const IndependentElementSet &other) const;

private:
  IndependentElementSet(const IndependentElementSet &ies) = default;
};

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
                                     const IndependentElementSet &ies) {
  ies.print(os);
  return os;
}

void getIndependentConstraints(const Query &query,
                               ConstraintSetView &resultView);

// Extracts which arrays are referenced from a particular independent set.
// Examines both
// the actual known array accesses arr[1] plus the undetermined accesses arr[x].
void calculateArrayReferences(const IndependentElementSet &ie,
                              std::vector<const Array *> &returnVector);
}
#endif /* KLEE_UTIL_INDEPENDENTELEMENTSET_H */
