/*
 * IncrementalSolver.cpp
 *
 * Solver allows incremental solving of equations.
 *
 * The general assumption is that constraints are ordered the way the are added.
 * And they keep this order.
 */

#include "klee/Solver.h"
#include "klee/SolverImpl.h"
#include "klee/SolverStats.h"
#include "klee/ExecutionState.h"
#include "klee/Expr.h"
#include "klee/Constraints.h"

#include <memory>

namespace klee {

class IncrementalSolverImpl : public SolverImpl {
private:
  std::unique_ptr<Solver> solver;
  ClientProcessAdapterSolver simpleAdapter;

  size_t use_index;

  const ExecutionState *oldState;
  std::unordered_set<ConstraintPosition> usedConstraints;

  ConstraintSetView activeConstraints;

public:
  IncrementalSolverImpl(Solver *_solver)
      : solver(_solver), simpleAdapter(nullptr, true, 1), use_index(0),
        oldState(nullptr) {
    solver->impl->setIncrementalStatus(true);
  }

  bool computeTruth(const Query &, bool &isValid) override;
  bool computeValidity(const Query &, Solver::Validity &result) override;
  bool computeValue(const Query &, ref<Expr> &result) override;
  bool computeInitialValues(const Query &query,
                            const std::vector<const Array *> &objects,
                            std::vector<std::vector<unsigned char> > &values,
                            bool &hasSolution) override;
  SolverRunStatus getOperationStatusCode() override;
  char *getConstraintLog(const Query &) override;
  void setCoreSolverTimeout(double timeout) override;

  void setIncrementalStatus(bool enable) override {
    solver->impl->setIncrementalStatus(enable);
  }

  bool getIncrementalStatus() override {
    return solver->impl->getIncrementalStatus();
  }

  void clearSolverStack() override {
    clearSolverStackAndState();
  }

  void clearSolverStackAndState(const ExecutionState * newState = nullptr) {
    usedConstraints.clear();

    // force clearing of solver stack
    solver->impl->clearSolverStack();
    oldState = newState;
  }
protected:
  Query getPartialQuery(const Query &q);
};

Query IncrementalSolverImpl::getPartialQuery(const Query &q) {
  bool clearedStack = false;

  use_index = 0;

  /* avoid over approximation, if there aren't any constraints,
   * we can't save anything */
  if (q.constraints.empty()) {
    use_index = 1;
    return q;
  }

  // In case we changed to a new state, we clear our saved state
  if (q.queryOrigin != oldState) {
    clearedStack = true;
  }
  //  else {
  //    // Check if used constraints were deleted
  //    for (auto pos : usedConstraints)
  //      if (q.constraints.isDeleted(pos)) {
  //        clearedStack = true;
  //        break;
  //      }
  //  }

  if (clearedStack) {
    clearSolverStackAndState(q.queryOrigin);
    q.incremental_flag = false;
  } else {
    q.incremental_flag = true;
  }
//  q.constraints.dump();

  SimpleConstraintManager cm(activeConstraints);
  cm.clear();

  size_t reused_cntr = 0;
  std::unordered_set<ConstraintPosition> newlyAddedConstraints;
  for (ConstraintSetView::const_iterator it = q.constraints.begin(),
                                         itE = q.constraints.end();
       it != itE; ++it) {
    auto position = q.constraints.getPositions(it);
//    llvm::errs() << "Position: " << position << "\n";
//    (*it)->dump();
    // Skip if we already used constraints from that position
    if (usedConstraints.count(position)) {
      ++reused_cntr;
      continue;
    }

    if (position.origin >= 0)
      newlyAddedConstraints.insert(position);

    cm.push_back(*it);
  }

  q.reused_cntr += reused_cntr;

  if (!reused_cntr && usedConstraints.size()) {
    use_index = 1;
    return q;
  }

  q.query_size = usedConstraints.size();
  usedConstraints.insert(newlyAddedConstraints.begin(), newlyAddedConstraints.end());
  if (!clearedStack) {
    ++stats::queryIncremental;
  }

  auto res = Query(activeConstraints, q.expr, q.queryOrigin);
//  llvm::errs() << "New query:\n";
//  res.dump();
  return res;
}

///

bool IncrementalSolverImpl::computeTruth(const Query &q, bool &isValid) {
  auto newQuery = getPartialQuery(q);
  if (!use_index)
    return solver->impl->computeTruth(newQuery, isValid);
  return simpleAdapter.impl->computeTruth(newQuery, isValid);
}

bool IncrementalSolverImpl::computeValidity(const Query &q,
                                            Solver::Validity &result) {
  auto newQuery = getPartialQuery(q);
  if (!use_index)
    return solver->impl->computeValidity(newQuery, result);
  return simpleAdapter.impl->computeValidity(newQuery, result);
}

bool IncrementalSolverImpl::computeValue(const Query &q, ref<Expr> &result) {
  auto newQuery = getPartialQuery(q);
  if (!use_index)
    return solver->impl->computeValue(newQuery, result);
  return simpleAdapter.impl->computeValue(newQuery, result);
}

bool IncrementalSolverImpl::computeInitialValues(
    const Query &query, const std::vector<const Array *> &objects,
    std::vector<std::vector<unsigned char> > &values, bool &hasSolution) {
  auto newQuery = getPartialQuery(query);
  if (!use_index)
    return solver->impl->computeInitialValues(newQuery, objects, values,
                                              hasSolution);
  return simpleAdapter.impl->computeInitialValues(newQuery, objects, values,
                                                  hasSolution);
}

SolverImpl::SolverRunStatus IncrementalSolverImpl::getOperationStatusCode() {
  if (!use_index)
    return solver->impl->getOperationStatusCode();
  return simpleAdapter.impl->getOperationStatusCode();
}

char *IncrementalSolverImpl::getConstraintLog(const Query &q) {
  auto newQuery = getPartialQuery(q);
  if (!use_index)
    return solver->impl->getConstraintLog(newQuery);
  return simpleAdapter.impl->getConstraintLog(newQuery);
}

void IncrementalSolverImpl::setCoreSolverTimeout(double timeout) {
  solver->impl->setCoreSolverTimeout(timeout);
  simpleAdapter.impl->setCoreSolverTimeout(timeout);
}

///

IncrementalSolver::IncrementalSolver(Solver *solver)
    : Solver(new IncrementalSolverImpl(solver)) {}

char *IncrementalSolver::getConstraintLog(const Query &q) {
  return impl->getConstraintLog(q);
}

void IncrementalSolver::setCoreSolverTimeout(double timeout) {
  impl->setCoreSolverTimeout(timeout);
}

} // namespace klee
