//===-- IndependentSolver.cpp ---------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "independent-solver"
#include "klee/Solver.h"

#include "klee/Expr.h"
#include "klee/Constraints.h"
#include "klee/SolverImpl.h"
#include "klee/Internal/Support/Debug.h"

#include "klee/util/ExprUtil.h"
#include "klee/util/Assignment.h"
#include "klee/util/IndependentElementSet.h"

#include "llvm/ADT/SparseBitVector.h"
#include "llvm/Support/raw_ostream.h"
#include <list>
#include <map>
#include <ostream>
#include <vector>

using namespace klee;
using namespace llvm;

class IndependentSolver : public SolverImpl {
private:
  Solver *solver;

public:
  IndependentSolver(Solver *_solver) 
    : solver(_solver) {}
  ~IndependentSolver() { delete solver; }

  bool computeTruth(const Query&, bool &isValid);
  bool computeValidity(const Query&, Solver::Validity &result);
  bool computeValue(const Query&, ref<Expr> &result);
  bool computeInitialValues(const Query& query,
                            const std::vector<const Array*> &objects,
                            std::vector< std::vector<unsigned char> > &values,
                            bool &hasSolution);
  SolverRunStatus getOperationStatusCode();
  char *getConstraintLog(const Query&);
  void setCoreSolverTimeout(double timeout);
  void setIncrementalStatus(bool enable) {
    solver->impl->setIncrementalStatus(enable);
  }

  bool getIncrementalStatus() { return solver->impl->getIncrementalStatus(); }

  void clearSolverStack() { solver->impl->clearSolverStack(); }
};
  
bool IndependentSolver::computeValidity(const Query& query,
                                        Solver::Validity &result) {
  ConstraintSetView required;
  getIndependentConstraints(query, required);
  return solver->impl->computeValidity(
      Query(required, query.expr, query.queryOrigin), result);
}

bool IndependentSolver::computeTruth(const Query& query, bool &isValid) {
  ConstraintSetView required;
  getIndependentConstraints(query, required);
  return solver->impl->computeTruth(
      Query(required, query.expr, query.queryOrigin), isValid);
}

bool IndependentSolver::computeValue(const Query& query, ref<Expr> &result) {
  ConstraintSetView required;
  getIndependentConstraints(query, required);
  return solver->impl->computeValue(
      Query(required, query.expr, query.queryOrigin), result);
}

// Helper function used only for assertions to make sure point created
// during computeInitialValues is in fact correct. The ``retMap`` is used
// in the case ``objects`` doesn't contain all the assignments needed.
bool assertCreatedPointEvaluatesToTrue(const Query &query,
                                       const std::vector<const Array*> &objects,
                                       std::vector< std::vector<unsigned char> > &values,
                                       std::map<const Array*, std::vector<unsigned char> > &retMap){
  Assignment assign = Assignment(objects, values);

  // Add any additional bindings.
  // The semantics of std::map should be to not insert a (key, value)
  // pair if it already exists so we should continue to use the assignment
  // from ``objects`` and ``values``.
  if (retMap.size() > 0)
    assign.bindings.insert(retMap.begin(), retMap.end());

  for (ConstraintSetView::constraint_iterator it = query.constraints.begin();
       it != query.constraints.end(); ++it) {
    // Do not force concretization of symbolic values, in that case we will end
    // up with a non ConstantExpr after evaluating the assignment and fail
    ref<Expr> ret = assign.evaluate(*it, false);

    assert(isa<ConstantExpr>(ret) && "assignment evaluation did not result in constant");
    ref<ConstantExpr> evaluatedConstraint = dyn_cast<ConstantExpr>(ret);
    if(evaluatedConstraint->isFalse()){
      return false;
    }
  }
  ref<Expr> neg = Expr::createIsZero(query.expr);
  ref<Expr> q = assign.evaluate(neg, false);
  assert(isa<ConstantExpr>(q) && "assignment evaluation did not result in constant");
  if (!cast<ConstantExpr>(q)->isTrue()) {
    llvm::errs() << "Query: \n";
    q->dump();
  }
  return cast<ConstantExpr>(q)->isTrue();
}

bool IndependentSolver::computeInitialValues(const Query& query,
                                             const std::vector<const Array*> &objects,
                                             std::vector< std::vector<unsigned char> > &values,
                                             bool &hasSolution){
  // We assume the query has a solution except proven differently
  // This is important in case we don't have any constraints but
  // we need initial values for requested array objects.
  hasSolution = true;

  std::list<IndependentElementSet> factors;
  getAllIndependentConstraintsSets(query, factors);

  //Used to rearrange all of the answers into the correct order
  std::map<const Array*, std::vector<unsigned char> > retMap;
  for (std::list<IndependentElementSet>::iterator it = factors.begin();
       it != factors.end(); ++it) {
    std::vector<const Array*> arraysInFactor;
    calculateArrayReferences(*it, arraysInFactor);
    // Going to use this as the "fresh" expression for the Query() invocation below
    assert(it->exprs.size() >= 1 && "No null/empty factors");
    if (arraysInFactor.size() == 0){
      continue;
    }
    ConstraintSetView tmp;
    for (auto e : it->exprs)
      tmp.constraints.push_back(e);
    std::vector<std::vector<unsigned char> > tempValues;
    if (!solver->impl->computeInitialValues(
            Query(tmp, ConstantExpr::alloc(0, Expr::Bool), query.queryOrigin),
            arraysInFactor, tempValues, hasSolution)) {
      values.clear();
      return false;
    } else if (!hasSolution){
      values.clear();
      return true;
    } else {
      assert(tempValues.size() == arraysInFactor.size() &&
             "Should be equal number arrays and answers");
      for (unsigned i = 0; i < tempValues.size(); i++){
        if (retMap.count(arraysInFactor[i])){
          // We already have an array with some partially correct answers,
          // so we need to place the answers to the new query into the right
          // spot while avoiding the undetermined values also in the array
          std::vector<unsigned char> * tempPtr = &retMap[arraysInFactor[i]];
          assert(tempPtr->size() == tempValues[i].size() &&
                 "we're talking about the same array here");
          auto *ds = &(it->elements[arraysInFactor[i]]);
          for (auto it2 = ds->begin(); it2 != ds->end(); it2++) {
            unsigned index = * it2;
            (* tempPtr)[index] = tempValues[i][index];
          }
        } else {
          // Dump all the new values into the array
          retMap[arraysInFactor[i]] = tempValues[i];
        }
      }
    }
  }
  for (std::vector<const Array *>::const_iterator it = objects.begin();
       it != objects.end(); it++){
    const Array * arr = * it;
    if (!retMap.count(arr)){
      // this means we have an array that is somehow related to the
      // constraint, but whose values aren't actually required to
      // satisfy the query.
      std::vector<unsigned char> ret(arr->size);
      values.push_back(ret);
    } else {
      values.push_back(retMap[arr]);
    }
  }
  assert(assertCreatedPointEvaluatesToTrue(query, objects, values, retMap) && "should satisfy the equation");
  return true;
}

SolverImpl::SolverRunStatus IndependentSolver::getOperationStatusCode() {
  return solver->impl->getOperationStatusCode();      
}

char *IndependentSolver::getConstraintLog(const Query& query) {
  return solver->impl->getConstraintLog(query);
}

void IndependentSolver::setCoreSolverTimeout(double timeout) {
  solver->impl->setCoreSolverTimeout(timeout);
}

Solver *klee::createIndependentSolver(Solver *s) {
  return new Solver(new IndependentSolver(s));
}
