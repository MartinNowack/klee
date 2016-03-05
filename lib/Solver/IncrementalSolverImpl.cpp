/*
 * IncrementalSolver.cpp
 *
 * Solver allows incremental solving of equations
 */

#include "klee/Solver.h"
#include "klee/SolverImpl.h"
#include "klee/SolverStats.h"
#include "klee/Expr.h"
#include "klee/Constraints.h"

#include <memory>

namespace klee {

class IncrementalSolverImpl : public SolverImpl {
private:
  std::unique_ptr<Solver> solver;

  const ExecutionState *oldState;
  std::vector<ref<Expr> > usedConstraints;
  std::vector<size_t> usedConstraintsStack;

  ConstraintManager activeConstraints;

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
    usedConstraints.clear();
    usedConstraintsStack.clear();

    // force clearing of solver stack
    solver->impl->clearSolverStack();
    oldState = nullptr;
  }

protected:
  Query getPartialQuery(const Query &q);
};

Query IncrementalSolverImpl::getPartialQuery(const Query &q) {
  // In case we change the state, we clear our saved state
  if (q.queryOrigin != oldState) {
    oldState = q.queryOrigin;
    clearSolverStack();
  }

  // Push new constraints
  auto oldIndex = usedConstraints.size();
  for (const auto e : q.constraints) {
    if (std::find(usedConstraints.begin(), usedConstraints.end(), &*e) ==
        usedConstraints.end())
      usedConstraints.push_back(&*e);
  }
  auto newIndex = usedConstraints.size();

  // Check if new constraints were added
  if (oldIndex != newIndex) {
    activeConstraints = ConstraintManager(usedConstraints.begin() + oldIndex,
                                          usedConstraints.begin() + newIndex);
    usedConstraintsStack.push_back(newIndex);
    ++stats::queryIncremental;
    return Query(activeConstraints, q.expr, q.queryOrigin);
  }
  activeConstraints = ConstraintManager();
  return Query(activeConstraints, q.expr, q.queryOrigin);
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
