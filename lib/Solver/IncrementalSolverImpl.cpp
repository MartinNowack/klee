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
#include "klee/util/ExprVisitor.h"
#include "klee/TimerStatIncrementer.h"

#include <memory>
#include <unordered_set>

namespace {
llvm::cl::opt<bool> NaiveIncremental(
    "naive-incremental",
    llvm::cl::desc("Ignore any solver failures (default=off)"),
    llvm::cl::init(false));
llvm::cl::opt<int>
    ParallelIncSolvers("parallel-incremental-solvers",
                       llvm::cl::desc("Ignore any solver failures (default=4)"),
                       llvm::cl::init(8));
}
namespace klee {

struct SolvingState {
  ClientProcessAdapterSolver *solver;

  std::vector<std::pair<ConstraintPosition, std::vector<const Array *> > >
      usedConstraints;

  std::vector<IndependentElementSet> used_expression;
  std::vector<std::vector<ConstraintPosition> > used_positions;

  // Track level of insertion
  std::vector<uint64_t> insertLevel;
  std::vector<std::pair<const Array *, uint64_t> > used_arrays;
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
      : max_solvers(ParallelIncSolvers), active_solvers(0),
        activeSolver(nullptr) {
    // Add basic core solver
    SolvingState state(solver);
    active_incremental_solvers.push_back(std::move(state));
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
      active_incremental_solvers.push_back(std::move(s));
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
  Query getPartialQuery_naive_incremental(const Query &q);

  Query getPartialQuery_simple_incremental(const Query &q);

  size_t selectBestSolver(const Query &q,
                          std::vector<std::vector<const Array *> > &objects,
                          size_t &non_conflict_level,
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

// if pos1 contains pos2
bool contains(const ConstraintPosition &pos1, const ConstraintPosition &pos2) {
  // if later id, it cannot contain
  if (pos2.constraint_id > pos1.constraint_id)
    return false;
  if (pos2.constraint_id <= pos1.constraint_id - pos1.constraint_width)
    return false;
  if (pos1.constraint_id == pos2.constraint_id && pos1.version != pos2.version)
    return false;
  return true;
}

class ExprCountVisitor : public ExprVisitor {
protected:
  Action visitRead(const ReadExpr &re) {
    const UpdateList &ul = re.updates;

    // XXX should we memo better than what ExprVisitor is doing for us?
    for (const UpdateNode *un = ul.head; un; un = un->next) {
      visit(un->index);
      visit(un->value);
    }

    if (ul.root->isSymbolicArray()) {
      auto pos =
          std::lower_bound(found_symbols.begin(), found_symbols.end(), ul.root);
      if (pos == found_symbols.end() || ul.root < *pos)
        found_symbols.insert(pos, ul.root);
    }

    return Action::doChildren();
  }

public:
  std::vector<const Array *> found_symbols;

  ExprCountVisitor() : ExprVisitor(true) {}
};

struct ConstraintPositionHashArray {
  size_t operator()(const std::pair<klee::ConstraintPosition,
                                    std::vector<const Array *> > &a) const {
    return std::hash<uint64_t>()(a.first.constraint_id);
  }
};

struct ConstraintPositionEqualArray {
  bool operator()(
      const std::pair<klee::ConstraintPosition, std::vector<const Array *> > &a,
      const std::pair<klee::ConstraintPosition, std::vector<const Array *> > &b)
      const {
    if (a.first.constraint_id != b.first.constraint_id)
      return false;
    if (a.first.constraint_width != b.first.constraint_width)
      return false;
    if (a.second != b.second)
      return false;
    return true;
  }
};

struct ConstraintPositionLessArray {
  bool operator()(
      const std::pair<klee::ConstraintPosition, std::vector<const Array *> > &a,
      const std::pair<klee::ConstraintPosition, std::vector<const Array *> > &b)
      const {
    if (a.first.constraint_id < b.first.constraint_id)
      return true;
    if (a.first.constraint_id == b.first.constraint_id &&
        a.first.constraint_width < b.first.constraint_width)
      return false;
    return true;
  }
};
size_t IncrementalSolverImpl::selectBestSolver(
    const Query &q, std::vector<std::vector<const Array *> > &used_arrays,
    size_t &non_conflict_level, size_t &reused_constraints,
    size_t &max_inactive) {
  // Handle available stack of solvers
  auto use_solver_index = active_solvers - 1;
  activeSolver = &active_incremental_solvers.back();

  std::vector<const Array *> usedArrays;

  for (const auto &o_pos : used_arrays) {
    for (auto sym : o_pos) {
      auto pos = std::lower_bound(usedArrays.begin(), usedArrays.end(), sym);
      if (pos == usedArrays.end() || sym < *pos)
        usedArrays.insert(pos, sym);
    }
  }

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

      const auto &position_solver = itSolverC->first;
      // Check if query contains new constraint not added yet
      // We do that in multiple steps:
      // 1) Check if it is a independent constraint
      // 2) Is related to the constraint

      if (position.constraint_id < position_solver.constraint_id) {
        // Check for case 1)
        if (position.constraint_id <= (position_solver.constraint_id -
                                       position_solver.constraint_width)) {
        } else if (used_arrays[std::distance(q.constraints.begin(), itQueryC)]
                       .size() < itSolverC->second.size()) {
          // Case 2)
          // We check if the number of symbolics changed
          // Case 2a) In case they do, we have to add the constraint
          // as this is the result from some transformation due to
          // other constraints, they might not be part of this query
        } else {
          assert(used_arrays[std::distance(q.constraints.begin(), itQueryC)]
                     .size() == itSolverC->second.size());
          // Case 2b) the number of symbolics is the same.
          // Therefore all constraints which might have been added,
          // will be part of this query.
          // We don't have to add this constraint
          //
          // Remember the level of the solver it was used
          constrain_levels.push_back(
              activeSolver->insertLevel[itSolverC -
                                        activeSolver->usedConstraints.begin()]);
        }

        ++itQueryC;
        continue;
      }

      // Check if the this constraint in the solver states conflict
      // and if its variables are conflicting with this query
      if (isSmaller(itSolverC->first, position)) {
        // for that, check if symbols in the constraint are used in the query
        for (auto symbol : itSolverC->second) {
          auto a_it =
              std::lower_bound(usedArrays.begin(), usedArrays.end(), symbol);
          if (a_it != usedArrays.end() && symbol == *a_it) {
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

      // In the following, we check equal constraints
      if (position.version != position_solver.version) {
        // XXX with a different version, we currently assume
        // even everything else equal, this will conflict
        conflictingLevel = std::min(
            conflictingLevel,
            activeSolver->insertLevel[itSolverC -
                                      activeSolver->usedConstraints.begin()] -
                1);

      } else {
        constrain_levels.push_back(
            activeSolver->insertLevel[itSolverC -
                                      activeSolver->usedConstraints.begin()]);
      }
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
      for (auto symbol : itSolverC->second) {
        auto a_it =
            std::lower_bound(usedArrays.begin(), usedArrays.end(), symbol);
        if (a_it != usedArrays.end() && symbol == *a_it) {
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

Query IncrementalSolverImpl::getPartialQuery_naive_incremental(
    const Query &q) {
  SimpleConstraintManager cm(activeConstraints);
  cm.clear();

  // We'll use the one solver available
  activeSolver = &active_incremental_solvers[1];

  // Generate big query iset
  IndependentElementSet query_constraint_iset;
  IndependentElementSet query_expr_iset(q.expr);

  std::set<ref<Expr> > constraints_to_add;
  std::set<ref<Expr> > constraints_to_remove;

  for (auto i = q.constraints.iset_begin(), e = q.constraints.iset_end();
       i != e; ++i) {
    query_constraint_iset.add(*i);
    constraints_to_add.insert((*i).exprs.begin(), (*i).exprs.end());
  }

  size_t reused = constraints_to_add.size();

  // Simple, we just check how many constraints we have in common and remove
  // the uncommon ones
  // Each indep set contains one stack frame of constraints
  size_t maxStackDepth = 0;
  for (auto &solver_frame : activeSolver->used_expression) {
    if (!solver_frame.intersects(query_constraint_iset) && !solver_frame.intersects(query_expr_iset)) {
      // if the solver stack frame doesn't intersect, we can keep that frame
      ++maxStackDepth;
      continue;
    }

    // if we have the same expression, we can use it
    // otherwise, we have to abort
    bool abort = false;
    std::vector<ref<Expr> > temp_found_expressions;
    for (auto expr : solver_frame.exprs) {
      // Check if we find that query in our constraints
      auto it =
          std::find(constraints_to_add.begin(), constraints_to_add.end(), expr);
      if (it != constraints_to_add.end()) {
        temp_found_expressions.push_back(expr);
        continue; // yes, check the next
      }

      // no, so we have to abort
      abort = true;
      break;
    }

    if (abort)
      break;

    // delete the found expressions
    constraints_to_remove.insert(temp_found_expressions.begin(), temp_found_expressions.end());
    ++maxStackDepth;
  }

  // Remove the remaining constraints
  for (auto & exp:constraints_to_remove)
    constraints_to_add.erase(exp);

  // Will use this solver
  // Update statistics and save constraints
  q.non_conflicting_cntr = activeSolver->usedConstraints.size();
  q.added_cntr = constraints_to_add.size();
  q.solver_id = activeSolver->solver_id;

  if (constraints_to_remove.empty())
	  maxStackDepth = 0;

  // Clean up previous levels
  activeSolver->used_expression.erase(activeSolver->used_expression.begin() +
                                          maxStackDepth,
                                      activeSolver->used_expression.end());

  //  llvm::errs() << "Level: " << maxStackDepth <<
  //      " I:" << !constraints_to_add.empty() << "\n";

  if (!constraints_to_add.empty()) {
    IndependentElementSet iset;
    for (auto &e : constraints_to_add) {
      iset.add(IndependentElementSet(e));
      cm.push_back(e);
    }
    activeSolver->used_expression.push_back(std::move(iset));
  }

  activeSolver->solver->impl->popStack(maxStackDepth);

  // We found one existing solver, update stats
  if (maxStackDepth) {
    ++stats::queryIncremental;
    q.incremental_flag = true;
    q.reused_cntr += (reused - constraints_to_add.size());
  }
  auto newQ = Query(activeConstraints, q.expr, q.queryOrigin);

  //  llvm::errs() << "Old query\n";
  //  q.dump();
  //
  //  llvm::errs() << "New query\n";
  //  newQ.dump();

  return newQ;
}

Query IncrementalSolverImpl::getPartialQuery_simple_incremental(
    const Query &q) {
  SimpleConstraintManager cm(activeConstraints);
  cm.clear();

  // Generate big query iset
  IndependentElementSet query_iset;
  IndependentElementSet expr_iset(q.expr);

  std::vector<ref<Expr> > constraints_to_add;
  std::vector<ConstraintPosition> constraint_position;

  // Generate new iset
  size_t iset_cntr = 0;
  for (auto i = q.constraints.iset_begin(), e = q.constraints.iset_end();
       i != e; ++i, ++iset_cntr) {
    query_iset.add(*i);
    // XXX we have a second copy of the sets here
    constraints_to_add.insert(constraints_to_add.end(), (*i).exprs.begin(),
                              (*i).exprs.end());
    constraint_position.insert(constraint_position.end(),
                               q.constraints.origPosition[iset_cntr].begin(),
                               q.constraints.origPosition[iset_cntr].end());
  }
  size_t constraints_of_query = constraints_to_add.size();

  // Select best suited solver
  std::vector<std::set<size_t> > solver_positions;
  solver_positions.push_back(std::set<size_t>());

  std::vector<size_t> solver_max_stack_depth;
  solver_max_stack_depth.push_back(0); // Handle 0 solver

  size_t max_inactive = 0;
  for (size_t solver_id = 1; solver_id < active_solvers; ++solver_id) {
    // Simple, we just check how many constraints we have in common and remove
    // the uncommon ones.
    //
    // Each stack frame of the solver is equivalent to one independent set for
    // it
    size_t maxStackDepth = 0;
    solver_positions.push_back(std::set<size_t>());
    //    std::set<size_t> positions;

    SolvingState *currentSolver = &active_incremental_solvers[solver_id];
    currentSolver->inactive++;

    max_inactive =
        (currentSolver->inactive > max_inactive ? currentSolver->inactive
                                                : max_inactive);

    for (auto &iset : currentSolver->used_expression) {
      // Check if this iset intersects with the query. In that case, we can
      // ignore it.
      bool iset_query_intersection = iset.intersects(query_iset);
      bool iset_expr_intersection = expr_iset.intersects(iset);
      if (!iset_query_intersection && !iset_expr_intersection) {
        // if it doesn't intersect, we can use that frame
        ++maxStackDepth;
        continue;
      }

      // if we have the same expression, we can use it
      // otherwise, we have to abort
      bool abort = false;

      std::vector<size_t> temp_found_expressions;
      auto expr_cntr = 0;

      // Now check if any constraint of this frame of the solver state
      // conflicts with a constraint of the query
      for (auto expr : iset.exprs) {
        // check if position is part of the query
        auto &solver_expr_position =
            currentSolver->used_positions[maxStackDepth][expr_cntr];
        bool found = false;
        for (auto pos_it = constraint_position.begin(),
                  pos_itE = constraint_position.end();
             pos_it != pos_itE; ++pos_it) {
          if (contains(solver_expr_position, *pos_it)) {
            found = true;
            temp_found_expressions.push_back(pos_it -
                                             constraint_position.begin());
            break;
          }
        }

        expr_cntr++;
        // We found it, so it's part of a previous constraint ignore it.
        if (found)
          continue;

        // Check if we find that query in our constraints
        auto it = std::find(constraints_to_add.begin(),
                            constraints_to_add.end(), expr);
        if (it != constraints_to_add.end()) {
          temp_found_expressions.push_back(it - constraints_to_add.begin());
          continue; // yes, check the next
        }

        // no, so we have to abort
        abort = true;
        break;
      }

      if (abort)
        break;

      // delete the found expressions
      solver_positions[solver_id].insert(temp_found_expressions.begin(),
                                         temp_found_expressions.end());
      ++maxStackDepth;
    }
    solver_max_stack_depth.push_back(maxStackDepth);
  }

  // Now select the best suitabel solver

  size_t max_reuse = 0;
  size_t best_solver = 0, current_solver = 0;
  for (auto &reuse : solver_positions) {
    if (reuse.size() > max_reuse) {
      max_reuse = reuse.size();
      best_solver = current_solver;
    }
    ++current_solver;
  }

  // none found, select the next free or reuse one
  size_t maxStackDepth = 0;

  if (!best_solver) {
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
  } else {
    activeSolver = &active_incremental_solvers[best_solver];
    for (auto i = solver_positions[best_solver].rbegin(),
              e = solver_positions[best_solver].rend();
         i != e; ++i) {
      constraints_to_add.erase(constraints_to_add.begin() + *i);
      constraint_position.erase(constraint_position.begin() + *i);
    }
    maxStackDepth = solver_max_stack_depth[best_solver];
  }

  auto oldStackHeight = activeSolver->used_expression.size();
  // Remove conflicting levels
  activeSolver->used_expression.erase(activeSolver->used_expression.begin() +
                                          maxStackDepth,
                                      activeSolver->used_expression.end());
  activeSolver->used_positions.erase(activeSolver->used_positions.begin() + maxStackDepth,
      activeSolver->used_positions.end());

  // Update LRU counter
  activeSolver->inactive = 0;

  // Update statistics and save constraints
  size_t solver_state_constraint_counter = 0;
  for (auto &i : activeSolver->used_expression)
    solver_state_constraint_counter += i.exprs.size();

  q.reused_cntr = solver_positions[best_solver].size();
  q.non_conflicting_cntr = solver_state_constraint_counter - q.reused_cntr;
  q.added_cntr = constraints_to_add.size() /* expr */;
  q.solver_id = activeSolver->solver_id;
  q.solver_state_stack_height = maxStackDepth;
  q.solver_stack_reduced = oldStackHeight - maxStackDepth;

  //  llvm::errs() << "Level: " << maxStackDepth <<
  //      " I:" << !constraints_to_add.empty() << "\n";

  if (!constraints_to_add.empty()) {
    IndependentElementSet iset;
    for (auto &e : constraints_to_add) {
      iset.add(IndependentElementSet(e));
      cm.push_back(e);
    }
    activeSolver->used_expression.push_back(std::move(iset));
    activeSolver->used_positions.push_back(constraint_position);
  }

  activeSolver->solver->impl->popStack(maxStackDepth);

  // We found one existing solver, update stats
  if (maxStackDepth) {
    ++stats::queryIncremental;
    q.incremental_flag = true;
  }
  auto newQ = Query(activeConstraints, q.expr, q.queryOrigin);

  //  llvm::errs() << "Old query\n";
  //  q.dump();
  //
  //  llvm::errs() << "New query\n";
  //  newQ.dump();

  return newQ;
}
Query IncrementalSolverImpl::getPartialQuery(const Query &q) {

  TimerStatIncrementer t(stats::queryIncCalculationTime);
  // avoid over approximation, if there aren't any constraints,
  // we can't save anything
  if (q.constraints.empty()) {
    activeSolver = &active_incremental_solvers[0];
    return q;
  }

  if (NaiveIncremental)
    return getPartialQuery_naive_incremental(q);
  return getPartialQuery_simple_incremental(q);

  SimpleConstraintManager cm(activeConstraints);
  std::vector<std::pair<ConstraintPosition, std::vector<const Array *> > >
      newlyAddedConstraints;

  // Acquire used Arrays per constraint
  std::vector<std::vector<const Array *> > used_arrays;
  for (auto &c : q.constraints) {
    ExprCountVisitor vis;
    vis.visit(c);
    used_arrays.push_back(vis.found_symbols);
  }

  // Check the incremental solvers
  size_t max_inactive = 0;

  size_t leastConflictingLevel = 0;
  size_t reuse = 0;
  auto pos = selectBestSolver(q, used_arrays, leastConflictingLevel, reuse,
                              max_inactive);

  if (leastConflictingLevel && pos) {
    activeSolver = &active_incremental_solvers[pos];

    // Prepare constraint manager
    // Clear constraints used in previous partial request
    cm.clear();

    // Check if we already have constraints in common and which are conflicting

    // ASSUMPTION: both vectors are in order
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

      if (position.constraint_id < position_solver.first.constraint_id) {
        // Check for case 1)
        if (position.constraint_id <=
            (position_solver.first.constraint_id -
             position_solver.first.constraint_width)) {
          newlyAddedConstraints.push_back(std::make_pair(
              position,
              used_arrays[std::distance(q.constraints.begin(), itQueryC)]));
          cm.push_back(*itQueryC);
        } else if (used_arrays[std::distance(q.constraints.begin(), itQueryC)]
                           .size() < position_solver.second.size() ||
                   constraintStackLevel > leastConflictingLevel) {
          // Case 2)
          // We check if the number of symbolics changed
          // Case 2a) In case they do, we have to add the constraint
          // as this is the result from some transformation due to
          // other constraints, they might not be part of this query
          newlyAddedConstraints.push_back(std::make_pair(
              position,
              used_arrays[std::distance(q.constraints.begin(), itQueryC)]));
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
      if (isSmaller(itSolverC->first, position)) {
        ++itSolverC;
        continue;
      }

      // Both positions are equal
      // Still, they might have to be added, if they will be removed
      if (constraintStackLevel > leastConflictingLevel) {
        newlyAddedConstraints.push_back(std::make_pair(
            position,
            used_arrays[std::distance(q.constraints.begin(), itQueryC)]));
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

      newlyAddedConstraints.push_back(std::make_pair(
          position,
          used_arrays[std::distance(q.constraints.begin(), itQueryC)]));
      cm.push_back(*itQueryC);
    }

    // Will use this solver
    // Update statistics and save constraints
    q.reused_cntr += reuse;
    q.non_conflicting_cntr = activeSolver->usedConstraints.size();
    q.added_cntr = newlyAddedConstraints.size();
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
      size_t idx = 0;
      for (auto new_pos : newlyAddedConstraints) {
        auto it = std::lower_bound(activeSolver->usedConstraints.begin(),
                                   activeSolver->usedConstraints.end(), new_pos,
                                   ConstraintPositionLessArray());
        activeSolver->insertLevel.insert(
            activeSolver->insertLevel.begin() +
                (it - activeSolver->usedConstraints.begin()),
            activeSolver->stackDepth);
        activeSolver->usedConstraints.insert(it, new_pos);
        ++idx;
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
    std::unordered_set<
        std::pair<ConstraintPosition, std::vector<const Array *> >,
        ConstraintPositionHashArray,
        ConstraintPositionEqualArray> newlyAddedConstraints;
    size_t idx = 0;
    for (ConstraintSetView::const_iterator it = q.constraints.begin(),
                                           itE = q.constraints.end();
         it != itE; ++it) {
      auto position = q.constraints.getPositions(it);

      newlyAddedConstraints.insert(std::make_pair(position, used_arrays[idx]));
      cm.push_back(*it);
      ++idx;
    }

    // sorted insert of used constraint positions
    activeSolver->usedConstraints.reserve(newlyAddedConstraints.size());
    activeSolver->insertLevel.reserve(newlyAddedConstraints.size());

    assert(used_arrays.size() == newlyAddedConstraints.size());
    for (auto new_pos : newlyAddedConstraints) {
      auto it = std::lower_bound(activeSolver->usedConstraints.begin(),
                                 activeSolver->usedConstraints.end(), new_pos,
                                 ConstraintPositionLessArray());
      activeSolver->usedConstraints.insert(it, new_pos);
      // Initialize level with 1;
      activeSolver->insertLevel.push_back(1);
    }
    activeSolver->stackDepth = 1;

    q.added_cntr = newlyAddedConstraints.size();
    q.solver_id = activeSolver->solver_id;
    activeSolver->inactive = 0;
    activeSolver->solver->impl->popStack(0);
  }

  if (q.constraints.size() != q.added_cntr + q.reused_cntr) {
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
  return solvers[0]->impl->getConstraintLog(q);
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
