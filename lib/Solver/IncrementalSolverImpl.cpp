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

  std::vector<ConstraintPosition> usedConstraints;

  // Track level of insertion
  std::vector<uint64_t> insertLevel;
  size_t stackDepth;
  size_t inactive;
  size_t solver_id;
  SolvingState(Solver *solver_)
      : solver(static_cast<ClientProcessAdapterSolver *>(solver_)),
        stackDepth(0), inactive(0), solver_id(0) {}
};

class IncrementalSolverImpl : public SolverImpl {
private:
  std::vector<SolvingState> active_incremental_solvers;
  std::vector<std::unique_ptr<ClientProcessAdapterSolver> > solvers;

  // Maximum number of solver instances to be used
  const size_t max_solvers;

  // Number of currently active solvers
  size_t active_solvers;

  // Index of solver from active_incremental_solvers to use
  SolvingState *activeSolver;

  // Used for any query during solving
  ConstraintSetView activeConstraints;

public:
  IncrementalSolverImpl(Solver *solver)
      : max_solvers(5), active_solvers(0), activeSolver(nullptr) {
    // Add basic core solver
    SolvingState state(solver);
    active_incremental_solvers.push_back(state);
    std::unique_ptr<ClientProcessAdapterSolver> ptr(
        static_cast<ClientProcessAdapterSolver *>(solver));
    solvers.push_back(std::move(ptr));

    // the base solver should not be incremental
    solver->impl->setIncrementalStatus(false);
    activeSolver = &active_incremental_solvers[0];
    ++active_solvers;

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
    state.insertLevel.clear();
    state.usedConstraints.clear();
    // force clearing of solver stack
    state.solver->impl->clearSolverStack();
  }

protected:
  Query getPartialQuery(const Query &q);
  size_t selectBestSolver(const Query &q, size_t &non_conflict_level,
                          size_t &reused_constraints, size_t &max_inactive);
};

bool isSmaller(const ConstraintPosition &pos1, const ConstraintPosition &pos2) {
  if (pos1.constraint_id < pos2.constraint_id)
    return true;
  if (pos1.constraint_id == pos2.constraint_id &&
      pos1.constraint_width < pos2.constraint_width)
    return true;
  return false;
}

size_t IncrementalSolverImpl::selectBestSolver(const Query &q,
                                               size_t &non_conflict_level,
                                               size_t &reused_constraints,
                                               size_t &max_inactive) {
  // Handle available stack of solvers
  auto use_solver_index = active_solvers - 1;
  activeSolver = &active_incremental_solvers.back();

  std::vector<const Array *> used_arrays = q.constraints.getUsedArrays();

  // Check the incremental solvers
  std::vector<size_t> conflictingLevels(active_solvers);
  std::vector<size_t> reuseCounters(active_solvers);


  while (use_solver_index > 0) {
    activeSolver = &active_incremental_solvers[use_solver_index--];
    assert(activeSolver != &active_incremental_solvers[0] &&
           "Don't use the non-incremental solver");

    // Update poor man's caching tracking
    max_inactive = std::max(++(activeSolver->inactive), max_inactive);

    // Check if we already have constraints in common and which are conflicting

    // ASSUMPTION: both vectors are in order
    auto itQueryC = q.constraints.begin();
    auto itEQueryC = q.constraints.end();

    auto itSolverC = activeSolver->usedConstraints.begin();
    auto itESolverC = activeSolver->usedConstraints.end();
    auto conflictingLevel = activeSolver->stackDepth;

    std::vector<size_t> constrain_levels;

    for (; itQueryC != itEQueryC && itSolverC != itESolverC;) {
      // TODO access positions directly
      auto position = q.constraints.getPositions(itQueryC);
      assert(position.constraint_id && "No position assigned");

      const auto &position_solver = *itSolverC;
      // Check if query contains new constraint not added yet
      // We do that in multiple steps:
      // 1) Check if it is a independent constraint
      // 2) Is related to the constraint

      if (position.constraint_id < position_solver.constraint_id) {
        // Check for case 1)
        if (position.constraint_id <= (position_solver.constraint_id -
                                       position_solver.constraint_width)) {
        } else if (position.contained_symbols.size() <
                   position_solver.contained_symbols.size()) {
          // Case 2)
          // We check if the number of symbolics changed
          // Case 2a) In case they do, we have to add the constraint
          // as this is the result from some transformation due to
          // other constraints, they might not be part of this query
        } else {
          assert(position.contained_symbols.size() ==
                 position_solver.contained_symbols.size());
          // Case 2b) the number of symbolics is the same.
          // Therefore all constraints which might have been added,
          // will be part of this query
          constrain_levels.push_back(
              activeSolver->insertLevel[itSolverC -
                                        activeSolver->usedConstraints.begin()]);
        }
        ++itQueryC;
        continue;
      }

      // Check if the constraint in the solver conflicts with this query
      if (isSmaller(*itSolverC, position)) {
        // for that, check if symbols in the constraint are used in the query
        for (auto symbol : itSolverC->contained_symbols) {
          auto a_it =
              std::lower_bound(used_arrays.begin(), used_arrays.end(), symbol);
          if (a_it != used_arrays.end() && symbol == *a_it) {

            conflictingLevel = std::min(
                conflictingLevel,
                activeSolver
                        ->insertLevel[itSolverC -
                                      activeSolver->usedConstraints.begin()] -
                    1);
          }
        }
        ++itSolverC;
        continue;
      }

      constrain_levels.push_back(
          activeSolver
              ->insertLevel[itSolverC - activeSolver->usedConstraints.begin()]);
      ++itQueryC;
      ++itSolverC;
    }

    // handle remaining query items
    for (; itQueryC != itEQueryC; ++itQueryC) {
    }

    // handle remaining solver items
    for (; itSolverC != itESolverC; ++itSolverC) {
      // Check if the constraint in the solver conflicts with this query
      // for that, check if symbols in the constraint are used in the query
      for (auto symbol : itSolverC->contained_symbols) {
        auto a_it =
            std::lower_bound(used_arrays.begin(), used_arrays.end(), symbol);
        if (a_it != used_arrays.end() && symbol == *a_it) {
          conflictingLevel = std::min(
              conflictingLevel,
              activeSolver->insertLevel[itSolverC -
                                        activeSolver->usedConstraints.begin()] -
                  1);
        }
      }
    }

    conflictingLevels[use_solver_index + 1] = conflictingLevel;
    reuseCounters[use_solver_index + 1] =
        std::count_if(constrain_levels.begin(), constrain_levels.end(),
                      [&](size_t i) { return (i <= conflictingLevel); });
  }

  // now, find the maximum reuse level here:
  auto max_reuse_it =
      std::max_element(reuseCounters.begin(), reuseCounters.end());
  auto solver_index = max_reuse_it - reuseCounters.begin();

  reused_constraints = *max_reuse_it;
  non_conflict_level = conflictingLevels[solver_index];

  // If no reuse is possible, select any solver
  if (!reused_constraints) {
    solver_index = 0;

  }
  return solver_index;
}

Query IncrementalSolverImpl::getPartialQuery(const Query &q) {
  // avoid over approximation, if there aren't any constraints,
  // we can't save anything
  if (q.constraints.empty()) {
    activeSolver = &active_incremental_solvers[0];
    return q;
  }

  SimpleConstraintManager cm(activeConstraints);
  std::vector<ConstraintPosition> newlyAddedConstraints;

  std::vector<const Array *> used_arrays = q.constraints.getUsedArrays();

  // Check the incremental solvers
  size_t max_inactive = 0;

  size_t leastConflictingLevel = 0;
  size_t reuse = 0;
  auto pos = selectBestSolver(q, leastConflictingLevel, reuse, max_inactive);

  if (leastConflictingLevel && pos) {
    activeSolver = &active_incremental_solvers[pos];

    // Prepare constraint manager
    // Clear constraints used in previous partial request
    cm.clear();

    // Check if we already have constraints in common and which are conflicting

    // ASSUMPTION: both vectors are in order
    newlyAddedConstraints.clear();
    auto itQueryC = q.constraints.begin();
    auto itEQueryC = q.constraints.end();

    auto itSolverC = activeSolver->usedConstraints.begin();
    auto itESolverC = activeSolver->usedConstraints.end();
    //    auto conflictingLevel = activeSolver->insertLevel.size();

    for (; itQueryC != itEQueryC && itSolverC != itESolverC;) {
      auto constraintStackLevel =
          activeSolver
              ->insertLevel[itSolverC - activeSolver->usedConstraints.begin()];

      // TODO access positions directly
      auto position = q.constraints.getPositions(itQueryC);
      assert(position.constraint_id && "No position assigned");

      const auto &position_solver = *itSolverC;
      // Check if query contains new constraint not added yet
      // We do that in multiple steps:
      // 1) Check if it is a independent constraint
      // 2) Is related to the constraint

      if (position.constraint_id < position_solver.constraint_id) {
        // Check for case 1)
        if (position.constraint_id <= (position_solver.constraint_id -
                                       position_solver.constraint_width)) {
          newlyAddedConstraints.push_back(position);
          cm.push_back(*itQueryC);
        } else if (position.contained_symbols.size() <
                       position_solver.contained_symbols.size() ||
                   constraintStackLevel > leastConflictingLevel) {
          // Case 2)
          // We check if the number of symbolics changed
          // Case 2a) In case they do, we have to add the constraint
          // as this is the result from some transformation due to
          // other constraints, they might not be part of this query
          newlyAddedConstraints.push_back(position);
          cm.push_back(*itQueryC);
        } else {
          // Case 2b) the number of symbolics is the same.
          // Therefore all constraints which might have been added,
          // will be part of this query
        }
        ++itQueryC;
        continue;
      }

      // Check if the constraint in the solver conflicts with this query
      if (isSmaller(*itSolverC, position)) {
        ++itSolverC;
        continue;
      }

      // Both positions are equal
      // Still, they might have to be added, if they will be removed
      if (constraintStackLevel > leastConflictingLevel) {
        newlyAddedConstraints.push_back(position);
        cm.push_back(*itQueryC);
      }
      ++itQueryC;
      ++itSolverC;
    }

    // handle remaining query items
    for (; itQueryC != itEQueryC; ++itQueryC) {
      // TODO access positions directly
      auto position = q.constraints.getPositions(itQueryC);
      assert(position.constraint_id && "No position assigned");

      newlyAddedConstraints.push_back(position);
      cm.push_back(*itQueryC);
    }

    // Will use this solver
    // Update statistics and save constraints
    q.reused_cntr += reuse;
    q.query_size = activeSolver->usedConstraints.size();
    q.added_constraints = newlyAddedConstraints.size();
    q.solver_id = activeSolver->solver_id;

    // Clean up previous levels
    for (auto it = activeSolver->insertLevel.begin();
         it != activeSolver->insertLevel.end();) {
      // Delete level
      if (*it <= leastConflictingLevel) {
        it++;
        continue;
      }
      // As we delete elements, we use indices
      // to update the iterators
      auto index = it - activeSolver->insertLevel.begin();
      activeSolver->insertLevel.erase(it);
      activeSolver->usedConstraints.erase(
          activeSolver->usedConstraints.begin() + index);
      it = activeSolver->insertLevel.begin() + index;
    }

    activeSolver->usedConstraints.reserve(activeSolver->usedConstraints.size() +
                                          newlyAddedConstraints.size());

    if (!newlyAddedConstraints.empty()) {
      // Add new level to the solver stack
      activeSolver->stackDepth = leastConflictingLevel + 1;
      for (auto new_pos : newlyAddedConstraints) {
        auto it = std::lower_bound(activeSolver->usedConstraints.begin(),
                                   activeSolver->usedConstraints.end(), new_pos,
                                   ConstraintPositionLess());
        activeSolver->insertLevel.insert(
            activeSolver->insertLevel.begin() +
                (it - activeSolver->usedConstraints.begin()),
            activeSolver->stackDepth);
        activeSolver->usedConstraints.insert(it, new_pos);
      }
    } else {
      // just reset to the least conflicting level
      activeSolver->stackDepth = leastConflictingLevel;
    }
    activeSolver->inactive = 0;
    activeSolver->solver->impl->popStack(leastConflictingLevel);
    // We found one existing solver, update stats
    ++stats::queryIncremental;
    q.incremental_flag = true;
  } else {
    // If we didn't find a solver yet, two options: add a new one or use an
    // existing one

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
    std::unordered_set<ConstraintPosition, ConstraintPositionHash,
                       ConstraintPositionEqual> newlyAddedConstraints;
    for (ConstraintSetView::const_iterator it = q.constraints.begin(),
                                           itE = q.constraints.end();
         it != itE; ++it) {
      auto position = q.constraints.getPositions(it);

      newlyAddedConstraints.insert(position);

      cm.push_back(*it);
    }

    // sorted insert of used constraint positions
    activeSolver->usedConstraints.reserve(newlyAddedConstraints.size());
    activeSolver->insertLevel.reserve(newlyAddedConstraints.size());
    for (auto new_pos : newlyAddedConstraints) {
      auto it = std::lower_bound(activeSolver->usedConstraints.begin(),
                                 activeSolver->usedConstraints.end(), new_pos,
                                 ConstraintPositionLess());
      activeSolver->usedConstraints.insert(it, new_pos);
      // Initialize leve with 1;
      activeSolver->insertLevel.push_back(1);
    }
    activeSolver->stackDepth = 1;

    q.added_constraints = newlyAddedConstraints.size();
    q.solver_id = activeSolver->solver_id;
    activeSolver->inactive = 0;
    activeSolver->solver->impl->popStack(0);
  }

  if (q.constraints.size() != q.added_constraints + q.reused_cntr) {
    q.dump();
    assert(0 && "Wrong size");
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
