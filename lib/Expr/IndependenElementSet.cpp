//===-- IndependentSolver.cpp ---------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "independent-solver"
#include "klee/Internal/Support/Debug.h"
#include "klee/util/IndependentElementSet.h"
#include "klee/util/ExprUtil.h"
#include "klee/TimerStatIncrementer.h"
#include "klee/SolverStats.h"

namespace klee {

IndependentElementSet::IndependentElementSet(ref<Expr> e) {
  exprs.push_back(e);
  // Track all reads in the program.  Determines whether reads are
  // concrete or symbolic.  If they are symbolic, "collapses" array
  // by adding it to wholeObjects.  Otherwise, creates a mapping of
  // the form Map<array, set<index>> which tracks which parts of the
  // array are being accessed.
  std::vector<ref<ReadExpr> > reads;
  findReads(e, /* visitUpdates= */ true, reads);
  for (unsigned i = 0; i != reads.size(); ++i) {
    ReadExpr *re = reads[i].get();
    const Array *array = re->updates.root;

    // Reads of a constant array don't alias.
    if (re->updates.root->isConstantArray() && !re->updates.head)
      continue;

    if (!wholeObjects.count(array)) {
      if (ConstantExpr *CE = dyn_cast<ConstantExpr>(re->index)) {
        // if index constant, then add to set of constraints operating
        // on that array (actually, don't add constraint, just set index)
        auto &dis = elements[array];
        dis.set((unsigned)CE->getZExtValue(32));
      } else {
        elements_ty::iterator it2 = elements.find(array);
        if (it2 != elements.end())
          elements.erase(it2);
        wholeObjects.insert(array);
      }
    }
  }
}
void IndependentElementSet::print(llvm::raw_ostream &os) const {
  os << "{";
  bool first = true;
  for (std::set<const Array *>::iterator it = wholeObjects.begin(),
                                         ie = wholeObjects.end();
       it != ie; ++it) {
    const Array *array = *it;

    if (first) {
      first = false;
    } else {
      os << ", ";
    }

    os << "MO" << array->name;
  }
  for (elements_ty::const_iterator it = elements.begin(), ie = elements.end();
       it != ie; ++it) {
    const Array *array = it->first;
    const auto &dis = it->second;

    if (first) {
      first = false;
    } else {
      os << ", ";
    }

    os << "MO" << array->name << " : ";
    llvm::dump(dis, os);
  }
  os << "}";
}

// more efficient when this is the smaller set
bool IndependentElementSet::intersects(const IndependentElementSet &b) const {
  // If there are any symbolic arrays in our query that b accesses
  for (std::set<const Array *>::const_iterator it = wholeObjects.begin(),
                                               ie = wholeObjects.end();
       it != ie; ++it) {
    const Array *array = *it;
    if (b.wholeObjects.count(array) ||
        b.elements.find(array) != b.elements.end())
      return true;
  }
  for (elements_ty::const_iterator it = elements.begin(), ie = elements.end();
       it != ie; ++it) {
    const Array *array = it->first;
    // if the array we access is symbolic in b
    if (b.wholeObjects.count(array))
      return true;
    elements_ty::const_iterator it2 = b.elements.find(array);
    // if any of the elements we access are also accessed by b
    if (it2 != b.elements.end()) {
      if (it->second.intersects(it2->second))
        return true;
    }
  }
  return false;
}

// returns true iff set is changed by addition
bool IndependentElementSet::add(const IndependentElementSet &b) {
  for (auto i = b.exprs.begin(), iE = b.exprs.end(); i != iE; ++i) {
    exprs.push_back(*i);
  }

  bool modified = false;
  for (std::set<const Array *>::const_iterator it = b.wholeObjects.begin(),
                                               ie = b.wholeObjects.end();
       it != ie; ++it) {
    const Array *array = *it;
    elements_ty::iterator it2 = elements.find(array);
    if (it2 != elements.end()) {
      modified = true;
      elements.erase(it2);
      wholeObjects.insert(array);
    } else {
      if (!wholeObjects.count(array)) {
        modified = true;
        wholeObjects.insert(array);
      }
    }
  }
  for (elements_ty::const_iterator it = b.elements.begin(),
                                   ie = b.elements.end();
       it != ie; ++it) {
    const Array *array = it->first;
    if (!wholeObjects.count(array)) {
      elements_ty::iterator it2 = elements.find(array);
      if (it2 == elements.end()) {
        modified = true;
        elements.insert(*it);
      } else {
        // Now need to see if there are any (z=?)'s
        if (it2->second != it->second)
          modified = true;
      }
    }
  }
  return modified;
}

// Breaks down a constraint into all of it's individual pieces, returning a
// list of IndependentElementSets or the independent factors.
//
// Caller takes ownership of returned std::list.

void getAllIndependentConstraintsSets(
    const Query &query, std::list<IndependentElementSet> &factors) {
  ConstantExpr *CE = dyn_cast<ConstantExpr>(query.expr);
  if (CE) {
    assert(CE && CE->isFalse() && "the expr should always be false and "
                                  "therefore not included in factors");
  } else {
    ref<Expr> neg = Expr::createIsZero(query.expr);
    factors.push_back(IndependentElementSet(neg));
  }

  for (ConstraintSetView::const_iterator it = query.constraints.begin(),
                                         ie = query.constraints.end();
       it != ie; ++it) {
    // iterate through all the previously separated constraints.  Until we
    // actually return, factors is treated as a queue of expressions to be
    // evaluated.  If the queue property isn't maintained, then the exprs
    // could be returned in an order different from how they came in, negatively
    // affecting later stages.
    factors.push_back(IndependentElementSet(*it));
  }

  bool doneLoop = false;
  do {
    doneLoop = true;
    std::list<IndependentElementSet> done;
    while (factors.size() > 0) {
      IndependentElementSet current = std::move(factors.front());
      factors.pop_front();
      // This list represents the set of factors that are separate from current.
      // Those that are not inserted into this list (queue) intersect with
      // current.
      std::list<IndependentElementSet> keep;
      while (factors.size() > 0) {
        IndependentElementSet compare = std::move(factors.front());
        factors.pop_front();
        if (current.intersects(compare)) {
          if (current.add(compare)) {
            // Means that we have added (z=y)added to (x=y)
            // Now need to see if there are any (z=?)'s
            doneLoop = false;
          }
        } else {
          keep.emplace_back(std::move(compare));
        }
      }
      done.emplace_back(std::move(current));
      factors.swap(keep);
    }
    factors.swap(done);
  } while (!doneLoop);
}

void getIndependentConstraints(const Query &query,
                               ConstraintSetView &resultView) {
  IndependentElementSet eltsClosure(query.expr);
  ReferencingConstraintManager result(resultView, query.constraints);
  std::vector<std::pair<ref<Expr>, IndependentElementSet> > worklist;
  worklist.reserve(query.constraints.size());

  for (ConstraintSetView::const_iterator it = query.constraints.begin(),
                                         ie = query.constraints.end();
       it != ie; ++it)
    worklist.push_back(std::make_pair(*it, IndependentElementSet(*it)));

  // XXX This should be more efficient (in terms of low level copy stuff).
  bool done = false;
  do {
    done = true;
    std::vector<std::pair<ref<Expr>, IndependentElementSet> > newWorklist;
    for (std::vector<std::pair<ref<Expr>, IndependentElementSet> >::iterator
             it = worklist.begin(),
             ie = worklist.end();
         it != ie; ++it) {
      if (it->second.intersects(eltsClosure)) {
        if (eltsClosure.add(it->second))
          done = false;
        result.push_back(it->first);
        // Means that we have added (z=y)added to (x=y)
        // Now need to see if there are any (z=?)'s
      } else {
        newWorklist.emplace_back(std::move(*it));
      }
    }
    if (!done)
      worklist.swap(newWorklist);
  } while (!done);

  KLEE_DEBUG(
      std::set<ref<Expr> > reqset(resultView.begin(), resultView.end());
      llvm::errs() << "--\n"; llvm::errs() << "Q: " << query.expr << "\n";
      llvm::errs() << "\telts: " << IndependentElementSet(query.expr) << "\n";
      int i = 0;
      for (ConstraintSetView::const_iterator it = query.constraints.begin(),
           ie = query.constraints.end();
           it != ie; ++it) {
        llvm::errs() << "C" << i++ << ": " << *it;
        llvm::errs() << " "
                     << (reqset.count(*it) ? "(required)" : "(independent)")
                     << "\n";
        llvm::errs() << "\telts: " << IndependentElementSet(*it) << "\n";
      } llvm::errs()
      << "elts closure: " << eltsClosure << "\n";);
}

// Extracts which arrays are referenced from a particular independent set.
// Examines both
// the actual known array accesses arr[1] plus the undetermined accesses arr[x].
void calculateArrayReferences(const IndependentElementSet &ie,
                              std::vector<const Array *> &returnVector) {
  std::set<const Array *> thisSeen;
  for (auto it = ie.elements.begin(); it != ie.elements.end(); it++) {
    thisSeen.insert(it->first);
  }
  for (std::set<const Array *>::iterator it = ie.wholeObjects.begin();
       it != ie.wholeObjects.end(); it++) {
    thisSeen.insert(*it);
  }
  for (std::set<const Array *>::iterator it = thisSeen.begin();
       it != thisSeen.end(); it++) {
    returnVector.push_back(*it);
  }
}
}
