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

struct SolvingState {
  ClientProcessAdapterSolver *solver;
  const ExecutionState *oldState;
  uint64_t state_uid;

  std::unordered_set<ConstraintPosition> usedConstraints;
  size_t inactive;
  size_t solver_id;
  SolvingState(Solver *solver_)
      : solver(static_cast<ClientProcessAdapterSolver *>(solver_)),
        oldState(nullptr), state_uid(0), inactive(0), solver_id(0) {}
};

class IncrementalSolverImpl : public SolverImpl {
private:
  std::vector<SolvingState> active_incremental_solvers;
  std::vector<std::unique_ptr<ClientProcessAdapterSolver> > solvers;

  const size_t max_solvers;
  size_t active_solvers;

  // Index of solver from active_incremental_solvers to use
  SolvingState *activeSolver;

  // Used for any query during solving
  ConstraintSetView activeConstraints;
public:
  IncrementalSolverImpl(Solver *solver)
      : max_solvers(10), active_solvers(1), activeSolver(nullptr) {
    // Add basic core solver
    SolvingState state(solver);
    active_incremental_solvers.push_back(state);
    std::unique_ptr<ClientProcessAdapterSolver> ptr(
        static_cast<ClientProcessAdapterSolver *>(solver));
    solvers.push_back(std::move(ptr));
    // the base solver should not be incremental
    solver->impl->setIncrementalStatus(false);
    activeSolver = &active_incremental_solvers[0];

    // Create and add additional solvers
    for (size_t i = 1; i < max_solvers; ++i) {
      std::unique_ptr<ClientProcessAdapterSolver> ptr(
          new ClientProcessAdapterSolver(nullptr, true, i));
      SolvingState s(ptr.get());
      s.solver->impl->setIncrementalStatus(true);
      s.solver_id = i;
      solvers.push_back(std::move(ptr));
      active_incremental_solvers.push_back(s);
    }
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
    // active_incremental_solvers[0].solver->impl->setIncrementalStatus(enable);
  }

  bool getIncrementalStatus() override {
    // return
    // active_incremental_solvers[0].solver->impl->getIncrementalStatus();
    return false;
  }

  void clearSolverStack() override {
    for (size_t i = 0; i < active_incremental_solvers.size(); ++i)
      clearSolverStackAndState(active_incremental_solvers[i]);
  }

  void clearSolverStackAndState(SolvingState &state,
                                const ExecutionState *newState = nullptr) {
    state.usedConstraints.clear();
    // force clearing of solver stack
    state.solver->impl->clearSolverStack();
    state.oldState = newState;
    state.state_uid = (newState ? newState->uid : 0);
  }

protected:
  Query getPartialQuery(const Query &q);
};

Query IncrementalSolverImpl::getPartialQuery(const Query &q) {
  // avoid over approximation, if there aren't any constraints,
  // we can't save anything
  if (q.constraints.empty()) {
    activeSolver = &active_incremental_solvers[0];
    return q;
  }

  // Handle available stack of solvers
  auto use_solver_index = active_solvers - 1;
  activeSolver = &active_incremental_solvers.back();

  SimpleConstraintManager cm(activeConstraints);
  std::unordered_set<ConstraintPosition> newlyAddedConstraints;

  // Check the incremental solvers
  bool found_solver = false;
  size_t max_inactive = 0;
  while (use_solver_index > 0) {
    activeSolver = &active_incremental_solvers[use_solver_index--];

    // Update poor man's caching tracking
    max_inactive = std::max(++(activeSolver->inactive), max_inactive);

    // Check if we have a state already known
    if (q.queryOrigin != activeSolver->oldState) {
      continue;
    }

    // Check if we have the same state but a different state_uid
    // This indicates that the state was deleted, a new one created
    // which has the same state as the old one
    if (q.queryOrigin && q.queryOrigin->uid != activeSolver->state_uid) {
      // TODO fix this
      continue;
    }

    // Prepare constraint manager
    // Clear constraints used in previous partial request
    cm.clear();

    // Handle this known state

    // Check if we already have constraints in common
    size_t reused_cntr = 0;
    newlyAddedConstraints.clear();
    for (ConstraintSetView::const_iterator it = q.constraints.begin(),
                                           itE = q.constraints.end();
         it != itE; ++it) {
      auto position = q.constraints.getPositions(it);

      // Skip if we already used constraints from that position
      if (activeSolver->usedConstraints.count(position)) {
        ++reused_cntr;
        continue;
      }

      if (position.origin >= 0)
        newlyAddedConstraints.insert(position);

      cm.push_back(*it);
    }

    // In case nothing found, try the next one
    if (!reused_cntr) {
      continue;
    }

    // Will use this solver
    // Update statistics and save constraints
    q.reused_cntr += reused_cntr;
    q.query_size = activeSolver->usedConstraints.size();
    q.added_constraints = newlyAddedConstraints.size();
    q.solver_id = activeSolver->solver_id;

    activeSolver->usedConstraints.insert(newlyAddedConstraints.begin(),
                                         newlyAddedConstraints.end());
    activeSolver->inactive = 0;
    found_solver = true;

    //    // we couldn't use the other solvers increment them as well
    //    while (use_solver_index > 0)
    //      active_incremental_solvers[use_solver_index--].inactive++;

    break;
  }

  // If we didn't find a solver yet, two options: add a new one or use an
  // existing one
  if (!found_solver) {
    // Check if we still have space for a new solver
    if (active_solvers < max_solvers) {
      // Yes, use the next free solver
      activeSolver = &active_incremental_solvers[active_solvers];
      ++active_solvers;
    } else {
      // No, search for the oldest unused one
      for (size_t i = 1; i < max_solvers; ++i) {
        if (active_incremental_solvers[i].inactive == max_inactive) {
          activeSolver = &active_incremental_solvers[i];
          break;
        }
      }
    }
    clearSolverStackAndState(*activeSolver, q.queryOrigin);
    q.incremental_flag = false;

    // Clear constraints used in previous partial request
    cm.clear();
    std::unordered_set<ConstraintPosition> newlyAddedConstraints;
    for (ConstraintSetView::const_iterator it = q.constraints.begin(),
                                           itE = q.constraints.end();
         it != itE; ++it) {
      auto position = q.constraints.getPositions(it);

      if (position.origin >= 0)
        newlyAddedConstraints.insert(position);

      cm.push_back(*it);
    }
    activeSolver->usedConstraints.insert(newlyAddedConstraints.begin(),
                                         newlyAddedConstraints.end());
    q.added_constraints = newlyAddedConstraints.size();
    q.solver_id = activeSolver->solver_id;
    activeSolver->inactive = 0;
  } else {
    // We found one existing solver, update stats
    ++stats::queryIncremental;
    q.incremental_flag = true;
  }

  auto res = Query(activeConstraints, q.expr, q.queryOrigin);
  return res;
}

///

bool IncrementalSolverImpl::computeTruth(const Query &q, bool &isValid) {
  auto newQuery = getPartialQuery(q);
  return activeSolver->solver->impl->computeTruth(newQuery, isValid);
}

bool IncrementalSolverImpl::computeValidity(const Query &q,
                                            Solver::Validity &result) {
  auto newQuery = getPartialQuery(q);
  return activeSolver->solver->impl->computeValidity(newQuery, result);
}

bool IncrementalSolverImpl::computeValue(const Query &q, ref<Expr> &result) {
  auto newQuery = getPartialQuery(q);
  return activeSolver->solver->impl->computeValue(newQuery, result);
}

bool IncrementalSolverImpl::computeInitialValues(
    const Query &query, const std::vector<const Array *> &objects,
    std::vector<std::vector<unsigned char> > &values, bool &hasSolution) {
  auto newQuery = getPartialQuery(query);
  return activeSolver->solver->impl->computeInitialValues(newQuery, objects,
                                                          values, hasSolution);
}

SolverImpl::SolverRunStatus IncrementalSolverImpl::getOperationStatusCode() {
  return activeSolver->solver->impl->getOperationStatusCode();
}

char *IncrementalSolverImpl::getConstraintLog(const Query &q) {
  auto newQuery = getPartialQuery(q);
  return activeSolver->solver->impl->getConstraintLog(newQuery);
}

void IncrementalSolverImpl::setCoreSolverTimeout(double timeout) {
  // We have to set the timeout of a potential future solver as well
  for (size_t i = 0; i < std::min(active_solvers + 1, max_solvers); ++i)
    active_incremental_solvers[i].solver->impl->setCoreSolverTimeout(timeout);
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
