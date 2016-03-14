/**
 * Test expression solving performance
 */

#include "benchmark/benchmark_api.h"

#include "klee/Expr.h"
#include "klee/Constraints.h"
#include "klee/Solver.h"
#include "klee/util/Serialization.h"

#include "llvm/ADT/StringExtras.h"

using namespace klee;
ref<Expr> getConstant(int value, Expr::Width width) {
  int64_t ext = value;
  uint64_t trunc = ext & (((uint64_t) -1LL) >> (64 - width));
  return ConstantExpr::create(trunc, width);
}

static void BM_createExpr(benchmark::State& state) {
  while (state.KeepRunning()) {
	  auto ar = Array::CreateArray("foo", 32);
	  auto ul = UpdateList(ar, nullptr);

          ConstraintSetView m;
          m.addConstraint(ReadExpr::create(ul, getConstant(0, 32)));
          m.addConstraint(ReadExpr::create(ul, getConstant(1,32)));

	  Query query(m, getConstant(3, 32), nullptr);

	  std::vector<const Array *> empty;
	  auto s = serializeQuery(query, empty);

          ConstraintSetView m2;
          auto query2 = deserializeQuery(s, m2);

          assert(m == m2);
	  assert(*query.expr == *query2.expr);
  }
}
// Register the function as a benchmark
BENCHMARK(BM_createExpr);
const int g_constants[] = { -1, 1, 4, 17, 0 };
const Expr::Width g_types[] = { Expr::Bool,
        Expr::Int8,
        Expr::Int16,
        Expr::Int32,
        Expr::Int64 };

template<class T>
void testOperation(Solver &solver,
                   int value,
                   Expr::Width operandWidth,
                   Expr::Width resultWidth) {
  std::vector<Expr::CreateArg> symbolicArgs;

  for (unsigned i = 0; i < T::numKids; i++) {
    if (!T::isValidKidWidth(i, operandWidth))
      return;

    unsigned size = Expr::getMinBytesForWidth(operandWidth);
    static uint64_t id = 0;
    const Array *array = Array::CreateArray("arr" + llvm::utostr(++id), size);
    symbolicArgs.push_back(Expr::CreateArg(Expr::createTempRead(array,
                                                                operandWidth)));
  }

  if (T::needsResultType())
    symbolicArgs.push_back(Expr::CreateArg(resultWidth));

  ref<Expr> fullySymbolicExpr = Expr::createFromKind(T::kind, symbolicArgs);

  // For each kid, replace the kid with a constant value and verify
  // that the fully symbolic expression is equivalent to it when the
  // replaced value is appropriated constrained.
  for (unsigned kid = 0; kid < T::numKids; kid++) {
    std::vector<Expr::CreateArg> partiallyConstantArgs(symbolicArgs);
    partiallyConstantArgs[kid] = getConstant(value, operandWidth);

    ref<Expr> expr =
      NotOptimizedExpr::create(EqExpr::create(partiallyConstantArgs[kid].expr,
                                              symbolicArgs[kid].expr));

    ref<Expr> partiallyConstantExpr =
      Expr::createFromKind(T::kind, partiallyConstantArgs);

    ref<Expr> queryExpr = EqExpr::create(fullySymbolicExpr,
                                         partiallyConstantExpr);

    ConstraintManager constraints;
    constraints.addConstraint(expr);
    bool res;
    bool success =
        solver.mustBeTrue(Query(constraints, queryExpr, nullptr), res);
    assert(true == success && "Constraint solving failed");

  }
}

template<class T>
void testOpcode(Solver &solver, bool tryBool = true, bool tryZero = true,
                unsigned maxWidth = 64) {
  for (unsigned j=0; j<sizeof(g_types)/sizeof(g_types[0]); j++) {
    Expr::Width type = g_types[j];

    if (type > maxWidth) continue;

    for (unsigned i=0; i<sizeof(g_constants)/sizeof(g_constants[0]); i++) {
      int value = g_constants[i];
      if (!tryZero && !value) continue;
      if (type == Expr::Bool && !tryBool) continue;

      if (!T::needsResultType()) {
        testOperation<T>(solver, value, type, type);
        continue;
      }

      for (unsigned k=0; k<sizeof(g_types)/sizeof(g_types[0]); k++) {
        Expr::Width resultType = g_types[k];

        // nasty hack to give only Trunc/ZExt/SExt the right types
        if (T::kind == Expr::SExt || T::kind == Expr::ZExt) {
          if (Expr::getMinBytesForWidth(type) >=
              Expr::getMinBytesForWidth(resultType))
            continue;
        }

        testOperation<T>(solver, value, type, resultType);
      }
    }
  }
}

static void BM_testCreateSolverCS(benchmark::State& state) {
  while (state.KeepRunning()) {
        Solver *solver = new ClientProcessAdapterSolver();
        solver = createIndependentSolver(solver);

        delete solver;
  }
}
//BENCHMARK(BM_testCreateSolverCS);

static void BM_testCreateSolver(benchmark::State& state) {
  while (state.KeepRunning()) {
        STPSolver *stpSolver = new STPSolver(true);
        Solver *solver = stpSolver;
        solver = createIndependentSolver(solver);

        delete solver;
  }
}
BENCHMARK(BM_testCreateSolver);



static void BM_testSolverCS(benchmark::State& state) {
  Solver *solver = new ClientProcessAdapterSolver();
  solver = createIndependentSolver(solver);

  while (state.KeepRunning()) {

    testOpcode<SelectExpr>(*solver);
    testOpcode<ZExtExpr>(*solver);
    testOpcode<SExtExpr>(*solver);

    testOpcode<AddExpr>(*solver);
    testOpcode<SubExpr>(*solver);
    testOpcode<MulExpr>(*solver, false, true, 8);
    testOpcode<SDivExpr>(*solver, false, false, 8);
    testOpcode<UDivExpr>(*solver, false, false, 8);
    testOpcode<SRemExpr>(*solver, false, false, 8);
    testOpcode<URemExpr>(*solver, false, false, 8);
    testOpcode<ShlExpr>(*solver, false);
    testOpcode<LShrExpr>(*solver, false);
    testOpcode<AShrExpr>(*solver, false);
    testOpcode<AndExpr>(*solver);
    testOpcode<OrExpr>(*solver);
    testOpcode<XorExpr>(*solver);

    testOpcode<EqExpr>(*solver);
    testOpcode<NeExpr>(*solver);
    testOpcode<UltExpr>(*solver);
    testOpcode<UleExpr>(*solver);
    testOpcode<UgtExpr>(*solver);
    testOpcode<UgeExpr>(*solver);
    testOpcode<SltExpr>(*solver);
    testOpcode<SleExpr>(*solver);
    testOpcode<SgtExpr>(*solver);
    testOpcode<SgeExpr>(*solver);
  }
  delete solver;
}
BENCHMARK(BM_testSolverCS);

static void BM_testSolverForked(benchmark::State& state) {
  STPSolver *stpSolver = new STPSolver(true);
  Solver *solver = stpSolver;
  solver = createIndependentSolver(solver);

  while (state.KeepRunning()) {

    testOpcode<SelectExpr>(*solver);
    testOpcode<ZExtExpr>(*solver);
    testOpcode<SExtExpr>(*solver);

    testOpcode<AddExpr>(*solver);
    testOpcode<SubExpr>(*solver);
    testOpcode<MulExpr>(*solver, false, true, 8);
    testOpcode<SDivExpr>(*solver, false, false, 8);
    testOpcode<UDivExpr>(*solver, false, false, 8);
    testOpcode<SRemExpr>(*solver, false, false, 8);
    testOpcode<URemExpr>(*solver, false, false, 8);
    testOpcode<ShlExpr>(*solver, false);
    testOpcode<LShrExpr>(*solver, false);
    testOpcode<AShrExpr>(*solver, false);
    testOpcode<AndExpr>(*solver);
    testOpcode<OrExpr>(*solver);
    testOpcode<XorExpr>(*solver);

    testOpcode<EqExpr>(*solver);
    testOpcode<NeExpr>(*solver);
    testOpcode<UltExpr>(*solver);
    testOpcode<UleExpr>(*solver);
    testOpcode<UgtExpr>(*solver);
    testOpcode<UgeExpr>(*solver);
    testOpcode<SltExpr>(*solver);
    testOpcode<SleExpr>(*solver);
    testOpcode<SgtExpr>(*solver);
    testOpcode<SgeExpr>(*solver);
  }

  delete solver;
}
BENCHMARK(BM_testSolverForked);

static void BM_testSolverUnforked(benchmark::State& state) {
  STPSolver *stpSolver = new STPSolver(false);
  Solver *solver = stpSolver;
  solver = createIndependentSolver(solver);

  while (state.KeepRunning()) {

    testOpcode<SelectExpr>(*solver);
    testOpcode<ZExtExpr>(*solver);
    testOpcode<SExtExpr>(*solver);

    testOpcode<AddExpr>(*solver);
    testOpcode<SubExpr>(*solver);
    testOpcode<MulExpr>(*solver, false, true, 8);
    testOpcode<SDivExpr>(*solver, false, false, 8);
    testOpcode<UDivExpr>(*solver, false, false, 8);
    testOpcode<SRemExpr>(*solver, false, false, 8);
    testOpcode<URemExpr>(*solver, false, false, 8);
    testOpcode<ShlExpr>(*solver, false);
    testOpcode<LShrExpr>(*solver, false);
    testOpcode<AShrExpr>(*solver, false);
    testOpcode<AndExpr>(*solver);
    testOpcode<OrExpr>(*solver);
    testOpcode<XorExpr>(*solver);

    testOpcode<EqExpr>(*solver);
    testOpcode<NeExpr>(*solver);
    testOpcode<UltExpr>(*solver);
    testOpcode<UleExpr>(*solver);
    testOpcode<UgtExpr>(*solver);
    testOpcode<UgeExpr>(*solver);
    testOpcode<SltExpr>(*solver);
    testOpcode<SleExpr>(*solver);
    testOpcode<SgtExpr>(*solver);
    testOpcode<SgeExpr>(*solver);
  }

  delete solver;
}
BENCHMARK(BM_testSolverUnforked);

static void BM_testSolverCSSingle(benchmark::State& state) {
  Solver *solver = new ClientProcessAdapterSolver();
  solver = createIndependentSolver(solver);

  while (state.KeepRunning()) {
    testOpcode<ZExtExpr>(*solver);
  }
  delete solver;
}
BENCHMARK(BM_testSolverCSSingle);

static void BM_testSolverForkedSingle(benchmark::State& state) {
  STPSolver *stpSolver = new STPSolver(true);
  Solver *solver = stpSolver;
  solver = createIndependentSolver(solver);

  while (state.KeepRunning()) {
    testOpcode<ZExtExpr>(*solver);
  }

  delete solver;
}
BENCHMARK(BM_testSolverForkedSingle);

static void BM_testSolverUnforkedSingle(benchmark::State& state) {
  STPSolver *stpSolver = new STPSolver(false);
  Solver *solver = stpSolver;
  solver = createIndependentSolver(solver);

  while (state.KeepRunning()) {
    testOpcode<ZExtExpr>(*solver);
  }

  delete solver;
}
BENCHMARK(BM_testSolverUnforkedSingle);

static void BM_testSolverCSAll(benchmark::State& state) {
  while (state.KeepRunning()) {
    Solver *solver = new ClientProcessAdapterSolver();
    solver = createIndependentSolver(solver);

    testOpcode<ZExtExpr>(*solver);

    delete solver;
  }
}
BENCHMARK(BM_testSolverCSAll);

BENCHMARK_MAIN()
