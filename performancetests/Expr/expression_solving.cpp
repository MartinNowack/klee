/**
 * Test expression solving performance
 */

#include "benchmark/benchmark_api.h"

#include "klee/Expr.h"
#include "klee/Constraints.h"
#include "klee/Solver.h"
#include "klee/util/Serialization.h"

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

	  ConstraintManager m;
	  m.addConstraint(ReadExpr::create(ul, getConstant(0,32)));
	  m.addConstraint(ReadExpr::create(ul, getConstant(1,32)));

	  Query query(m, getConstant(3, 32), nullptr);

	  std::vector<const Array *> empty;
	  auto s = serializeQuery(query, empty);

	  ConstraintManager m2;
	  auto query2 = deserializeQuery(s, m2);

	  assert(m == m2);
	  assert(*query.expr == *query2.expr);
  }
}
// Register the function as a benchmark
BENCHMARK(BM_createExpr);

BENCHMARK_MAIN()
