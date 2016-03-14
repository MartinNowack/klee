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

  const ExecutionState *oldState;
  std::set<int64_t> usedConstraints;

  ConstraintSetView activeConstraints;

public:
  IncrementalSolverImpl(Solver *_solver) : solver(_solver), oldState(nullptr) {
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

  // In case we changed to a new state, we clear our saved state
  if (q.queryOrigin != oldState) {
    clearedStack = true;
  } else {
    // Check if used constraints were deleted
    for (auto pos : usedConstraints)
      if (q.constraints.isDeleted(pos)) {
        clearedStack = true;
        break;
      }
  }

  if (clearedStack)
    clearSolverStackAndState(q.queryOrigin);

  SimpleConstraintManager cm(activeConstraints);
  cm.clear();

  for (ConstraintSetView::const_iterator it = q.constraints.begin(),
                                         itE = q.constraints.end();
       it != itE; ++it) {
    auto position = q.constraints.getPositions(it);
    // Skip if we already used that constraint
    if (usedConstraints.count(position))
      continue;

    if (position >= 0)
      usedConstraints.insert(position);
    cm.push_back(*it);
  }

  if (!clearedStack) {
    ++stats::queryIncremental;
  }

  auto res = Query(activeConstraints, q.expr, q.queryOrigin);
  return res;
}

///

bool IncrementalSolverImpl::computeTruth(const Query &q, bool &isValid) {
  auto newQuery = getPartialQuery(q);
  return solver->impl->computeTruth(newQuery, isValid);
}

bool IncrementalSolverImpl::computeValidity(const Query &q,
                                            Solver::Validity &result) {
  auto newQuery = getPartialQuery(q);
  return solver->impl->computeValidity(newQuery, result);
}

bool IncrementalSolverImpl::computeValue(const Query &q, ref<Expr> &result) {
  auto newQuery = getPartialQuery(q);
  return solver->impl->computeValue(newQuery, result);
}

bool IncrementalSolverImpl::computeInitialValues(
    const Query &query, const std::vector<const Array *> &objects,
    std::vector<std::vector<unsigned char> > &values, bool &hasSolution) {
  auto newQuery = getPartialQuery(query);
  return solver->impl->computeInitialValues(newQuery, objects, values,
                                            hasSolution);
}

SolverImpl::SolverRunStatus IncrementalSolverImpl::getOperationStatusCode() {
  return solver->impl->getOperationStatusCode();
}

char *IncrementalSolverImpl::getConstraintLog(const Query &q) {
  auto newQuery = getPartialQuery(q);
  return solver->impl->getConstraintLog(newQuery);
}

void IncrementalSolverImpl::setCoreSolverTimeout(double timeout) {
  solver->impl->setCoreSolverTimeout(timeout);
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
