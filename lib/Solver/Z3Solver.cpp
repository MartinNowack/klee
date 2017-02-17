//===-- Z3Solver.cpp -------------------------------------------*- C++ -*-====//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "klee/Config/config.h"
#include "klee/Internal/Support/ErrorHandling.h"
#ifdef ENABLE_Z3
#include "Z3Builder.h"
#include "klee/Constraints.h"
#include "klee/Solver.h"
#include "klee/SolverImpl.h"
#include "klee/util/Assignment.h"
#include "klee/util/ExprUtil.h"

#include "llvm/Support/ErrorHandling.h"
namespace {
llvm::cl::opt<bool> DebugDumpZ3Queries(
    "debug-dump-z3-queries", llvm::cl::init(false),
    llvm::cl::desc("Dump every Z3 query to stderr (default=off)"));
}
namespace klee {

class Z3SolverImpl : public SolverImpl {
private:
  Z3Builder *builder;
  ::Z3_solver theSolver;
  double timeout;
  SolverRunStatus runStatusCode;
  ::Z3_params solverParameters;
  // Parameter symbols
  ::Z3_symbol timeoutParamStrSymbol;

  bool internalRunSolver(const Query &,
                         const std::vector<const Array *> *objects,
                         std::vector<std::vector<unsigned char> > *values,
                         bool &hasSolution);
  void printZ3Query();

public:
  Z3SolverImpl();
  ~Z3SolverImpl();

  char *getConstraintLog(const Query &);
  void setCoreSolverTimeout(double _timeout) {
    return;
    assert(_timeout >= 0.0 && "timeout must be >= 0");
    timeout = _timeout;

    unsigned int timeoutInMilliSeconds = (unsigned int)((timeout * 1000) + 0.5);
    if (timeoutInMilliSeconds == 0)
      timeoutInMilliSeconds = UINT_MAX;
    Z3_params_set_uint(builder->ctx, solverParameters, timeoutParamStrSymbol,
                       timeoutInMilliSeconds);
  }

  bool computeTruth(const Query &, bool &isValid);
  bool computeValue(const Query &, ref<Expr> &result);
  bool computeInitialValues(const Query &,
                            const std::vector<const Array *> &objects,
                            std::vector<std::vector<unsigned char> > &values,
                            bool &hasSolution);
  SolverRunStatus
  handleSolverResponse(::Z3_solver theSolver, ::Z3_lbool satisfiable,
                       const std::vector<const Array *> *objects,
                       std::vector<std::vector<unsigned char> > *values,
                       bool &hasSolution);
  SolverRunStatus getOperationStatusCode();
  bool incremental;
  size_t inc_index;
  void setIncrementalStatus(bool enable) {
    incremental = enable;
  }
  bool getIncrementalStatus() {
    return incremental;
  }

  void clearSolverStack() {
    builder->clearConstructCache();
    popStack(0);
  }

  void popStack(size_t until_index) {
    if (until_index == 0) {
      Z3_solver_reset(builder->ctx, theSolver);
      inc_index = 0;
      return;
    }
    assert(until_index <= inc_index);
    Z3_solver_pop(builder->ctx, theSolver, inc_index - until_index);
    inc_index = until_index;
  }
};

Z3SolverImpl::Z3SolverImpl()
    : builder(new Z3Builder(/*autoClearConstructCache=*/false)), timeout(0.0),
      runStatusCode(SOLVER_RUN_STATUS_FAILURE), inc_index(0) {
  assert(builder && "unable to create Z3Builder");
  solverParameters = Z3_mk_params(builder->ctx);
  Z3_params_inc_ref(builder->ctx, solverParameters);
  timeoutParamStrSymbol = Z3_mk_string_symbol(builder->ctx, "timeout");
  setCoreSolverTimeout(timeout);
  ::Z3_symbol logic_str = Z3_mk_string_symbol(builder->ctx, "QF_AUFBV");
  theSolver = Z3_mk_solver_for_logic(builder->ctx, logic_str);
  Z3_solver_inc_ref(builder->ctx, theSolver);
  Z3_solver_set_params(builder->ctx, theSolver, solverParameters);

}

Z3SolverImpl::~Z3SolverImpl() {
  Z3_solver_dec_ref(builder->ctx, theSolver);
  Z3_params_dec_ref(builder->ctx, solverParameters);
  delete builder;
}

Z3Solver::Z3Solver() : Solver(new Z3SolverImpl()) {}

char *Z3Solver::getConstraintLog(const Query &query) {
  return impl->getConstraintLog(query);
}

void Z3Solver::setCoreSolverTimeout(double timeout) {
  impl->setCoreSolverTimeout(timeout);
}

char *Z3SolverImpl::getConstraintLog(const Query &query) {
  std::vector<Z3ASTHandle> assumptions;
  for (auto it = query.constraints.begin(), ie = query.constraints.end();
       it != ie; ++it) {
    assumptions.push_back(builder->construct(*it));
  }
  ::Z3_ast *assumptionsArray = NULL;
  int numAssumptions = query.constraints.size();
  if (numAssumptions) {
    assumptionsArray = (::Z3_ast *)malloc(sizeof(::Z3_ast) * numAssumptions);
    for (int index = 0; index < numAssumptions; ++index) {
      assumptionsArray[index] = (::Z3_ast)assumptions[index];
    }
  }

  // KLEE Queries are validity queries i.e.
  // ∀ X Constraints(X) → query(X)
  // but Z3 works in terms of satisfiability so instead we ask the
  // the negation of the equivalent i.e.
  // ∃ X Constraints(X) ∧ ¬ query(X)
  Z3ASTHandle formula = Z3ASTHandle(
      Z3_mk_not(builder->ctx, builder->construct(query.expr)), builder->ctx);

  ::Z3_string result = Z3_benchmark_to_smtlib_string(
      builder->ctx,
      /*name=*/"Emited by klee::Z3SolverImpl::getConstraintLog()",
      /*logic=*/"",
      /*status=*/"unknown",
      /*attributes=*/"",
      /*num_assumptions=*/numAssumptions,
      /*assumptions=*/assumptionsArray,
      /*formula=*/formula);

  if (numAssumptions)
    free(assumptionsArray);
  // Client is responsible for freeing the returned C-string
  return strdup(result);
}

bool Z3SolverImpl::computeTruth(const Query &query, bool &isValid) {
  bool hasSolution;
  bool status =
      internalRunSolver(query, /*objects=*/NULL, /*values=*/NULL, hasSolution);
  isValid = !hasSolution;
  return status;
}

bool Z3SolverImpl::computeValue(const Query &query, ref<Expr> &result) {
  std::vector<const Array *> objects;
  std::vector<std::vector<unsigned char> > values;
  bool hasSolution;

  // Find the object used in the expression, and compute an assignment
  // for them.
  findSymbolicObjects(query.expr, objects);
  if (!computeInitialValues(query.withFalse(), objects, values, hasSolution))
    return false;
  assert(hasSolution && "state has invalid constraint set");

  // Evaluate the expression with the computed assignment.
  Assignment a(objects, values);
  result = a.evaluate(query.expr, true);

  return true;
}

bool Z3SolverImpl::computeInitialValues(
    const Query &query, const std::vector<const Array *> &objects,
    std::vector<std::vector<unsigned char> > &values, bool &hasSolution) {
  return internalRunSolver(query, &objects, &values, hasSolution);
}

void Z3SolverImpl::printZ3Query() {
  if (!DebugDumpZ3Queries)
    return;
  static size_t query_id = 0;
  llvm::errs() << "\nQuery\n" << query_id++ << "\n";
  ::Z3_ast_vector svector = Z3_solver_get_assertions(builder->ctx, theSolver);
  for (size_t i = 0, j = Z3_ast_vector_size(builder->ctx, svector); i < j;
       ++i) {
    llvm::errs() << Z3_ast_to_string(
                        builder->ctx,
                        Z3_ast_vector_get(builder->ctx, svector, i))
                 << "\n";
  }
}

bool Z3SolverImpl::internalRunSolver(
    const Query &query, const std::vector<const Array *> *objects,
    std::vector<std::vector<unsigned char> > *values, bool &hasSolution) {
  TimerStatIncrementer t(stats::queryTime);

  if (!incremental || !inc_index) {
    Z3_solver_reset(builder->ctx, theSolver);
    inc_index = 0;
    assert(Z3_solver_get_num_scopes(builder->ctx, theSolver) == 0);
  }

  runStatusCode = SOLVER_RUN_STATUS_FAILURE;

  if (incremental && !query.constraints.empty()) {
    // Keep the first layer without extra context to use faster solver
    if (inc_index)
      Z3_solver_push(builder->ctx, theSolver);
    ++inc_index;
  }

  // Put all constraints on the solver state
  for (ConstraintSetView::const_iterator it = query.constraints.begin(),
                                         ie = query.constraints.end();
       it != ie; ++it) {
    Z3_solver_assert(builder->ctx, theSolver, builder->construct(*it));
  }
  ++stats::queries;
  if (objects)
    ++stats::queryCounterexamples;

  // If the query is false, don't add it as another constraint
  // nor push() a new solver context
  bool addedImplicationContext = false;
  if (query.expr != ConstantExpr::alloc(0, Expr::Bool)) {
    // Open a new context  for the implication
    if (incremental) {
      Z3_solver_push(builder->ctx, theSolver);
      ++inc_index;
      addedImplicationContext = true;
    }

    // KLEE Queries are validity queries i.e.
    // ∀ X Constraints(X) → query(X)
    // but Z3 works in terms of satisfiability so instead we ask the
    // negation of the equivalent i.e.
    // ∃ X Constraints(X) ∧ ¬ query(X)
    Z3ASTHandle z3QueryExpr =
        Z3ASTHandle(builder->construct(query.expr), builder->ctx);
    Z3_solver_assert(
        builder->ctx, theSolver,
        Z3ASTHandle(Z3_mk_not(builder->ctx, z3QueryExpr), builder->ctx));
  }

  ::Z3_lbool satisfiable = Z3_solver_check(builder->ctx, theSolver);
  runStatusCode = handleSolverResponse(theSolver, satisfiable, objects, values,
                                       hasSolution);
  printZ3Query();

  if (addedImplicationContext) {
    // Remove context for implication
    Z3_solver_pop(builder->ctx, theSolver, 1);
    --inc_index;
  }

  // Clear the builder's cache to prevent memory usage exploding.
  // By using ``autoClearConstructCache=false`` and clearing now
  // we allow Z3_ast expressions to be shared from an entire
  // ``Query`` rather than only sharing within a single call to
  // ``builder->construct()``.
  if (!incremental)
    builder->clearConstructCache();

  if (runStatusCode == SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE ||
      runStatusCode == SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE) {
    if (hasSolution) {
      ++stats::queriesInvalid;
    } else {
      ++stats::queriesValid;
    }
    return true; // success
  }
  return false; // failed
}

SolverImpl::SolverRunStatus Z3SolverImpl::handleSolverResponse(
    ::Z3_solver theSolver, ::Z3_lbool satisfiable,
    const std::vector<const Array *> *objects,
    std::vector<std::vector<unsigned char> > *values, bool &hasSolution) {
  switch (satisfiable) {
  case Z3_L_TRUE: {
    hasSolution = true;
    if (!objects) {
      // No assignment is needed
      assert(values == NULL);
      return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
    }
    assert(values && "values cannot be nullptr");
    ::Z3_model theModel = Z3_solver_get_model(builder->ctx, theSolver);
    assert(theModel && "Failed to retrieve model");
    Z3_model_inc_ref(builder->ctx, theModel);
    values->reserve(objects->size());
    for (std::vector<const Array *>::const_iterator it = objects->begin(),
                                                    ie = objects->end();
         it != ie; ++it) {
      const Array *array = *it;
      std::vector<unsigned char> data;

      data.reserve(array->size);
      for (unsigned offset = 0; offset < array->size; offset++) {
        // We can't use Z3ASTHandle here so have to do ref counting manually
        ::Z3_ast arrayElementExpr;
        Z3ASTHandle initial_read = builder->getInitialRead(array, offset);

        bool successfulEval =
            Z3_model_eval(builder->ctx, theModel, initial_read,
                          /*model_completion=*/Z3_TRUE, &arrayElementExpr);
        assert(successfulEval && "Failed to evaluate model");
        Z3_inc_ref(builder->ctx, arrayElementExpr);
        assert(Z3_get_ast_kind(builder->ctx, arrayElementExpr) ==
                   Z3_NUMERAL_AST &&
               "Evaluated expression has wrong sort");

        int arrayElementValue = 0;
        bool successGet = Z3_get_numeral_int(builder->ctx, arrayElementExpr,
                                             &arrayElementValue);
        assert(successGet && "failed to get value back");
        assert(arrayElementValue >= 0 && arrayElementValue <= 255 &&
               "Integer from model is out of range");
        data.push_back(arrayElementValue);
        Z3_dec_ref(builder->ctx, arrayElementExpr);
      }
      values->push_back(data);
    }

    Z3_model_dec_ref(builder->ctx, theModel);
    return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
  }
  case Z3_L_FALSE:
    hasSolution = false;
    return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
  case Z3_L_UNDEF: {
    ::Z3_string reason =
        ::Z3_solver_get_reason_unknown(builder->ctx, theSolver);
    if (strcmp(reason, "timeout") == 0 || strcmp(reason, "canceled") == 0) {
      return SolverImpl::SOLVER_RUN_STATUS_TIMEOUT;
    }
    if (strcmp(reason, "unknown") == 0) {
      return SolverImpl::SOLVER_RUN_STATUS_FAILURE;
    }
    klee_warning("Unexpected solver failure. Reason is \"%s,\"\n", reason);
    abort();
  }
  default:
    llvm_unreachable("unhandled Z3 result");
  }
}

SolverImpl::SolverRunStatus Z3SolverImpl::getOperationStatusCode() {
  return runStatusCode;
}
}
#endif // ENABLE_Z3
