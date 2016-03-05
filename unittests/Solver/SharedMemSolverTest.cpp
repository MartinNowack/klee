//===-- SolverTest.cpp ----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "gtest/gtest.h"

#include "klee/Constraints.h"
#include "klee/Expr.h"
#include "klee/Solver.h"
#include "klee/SolverImpl.h"
#include "klee/util/ArrayCache.h"
#include "klee/util/SharedMemory.h"
#include "klee/util/Serialization.h"

#include <cstdint>
using namespace klee;

namespace {
ref<ConstantExpr> getConstant(int value, Expr::Width width) {
  int64_t ext = value;
  uint64_t trunc = ext & (((uint64_t)-1LL) >> (64 - width));
  return ConstantExpr::create(trunc, width);
}

TEST(SolverTest, SharedMemoryExpression) {
  ArrayCache cache;
  // Two shared memory regions pointing to the same area
  SharedMem m(SharedMem::defaultSize);
  SharedMem m2(SharedMem::defaultSize);

  EXPECT_TRUE(m.getAddr() == m.getAddr());
  EXPECT_TRUE(m2.getAddr() != m.getAddr());

  auto exp1 = getConstant(42, 32);

  auto s = serializeExpression(exp1);
  EXPECT_TRUE(*exp1 == *deserializeExpression(s, &cache));

  Serializer ser(m);
  Deserializer deser1(m, &cache);
  Deserializer deser2(m2, &cache);

  bool success = true;
  bool success2;
  ser.serializeExpression(exp1, success);
  // Deserialize from first shared memory area
  EXPECT_TRUE(*exp1 == *deser1.deserializeExpression(success2));
  EXPECT_TRUE(success2);

  // Deserialize from second shared memory area
  EXPECT_TRUE(*exp1 == *deser2.deserializeExpression(success2));
  EXPECT_TRUE(success2);
}

TEST(SolverTest, SharedMemoryQuery) {
  ArrayCache cache;
  // Two shared memory regions pointing to the same area
  SharedMem sm(SharedMem::defaultSize);
  SharedMem sm2(SharedMem::defaultSize);
  Serializer ser(sm);
  Deserializer deser(sm2, &cache);

  EXPECT_TRUE(sm2.getAddr() != sm.getAddr());

  auto ar = cache.CreateArray("foo", 32);
  auto ul = UpdateList(ar, nullptr);

  ConstraintManager m;
  m.addConstraint(ReadExpr::create(ul, getConstant(0, 32)));
  m.addConstraint(ReadExpr::create(ul, getConstant(1, 32)));

  Query query(m, getConstant(3, 32), nullptr);

  std::vector<const Array *> empty;
  ser.serializeQuery(query, empty);

  ConstraintManager m2;
  auto query2 = deser.deserializeQuery(m2);

  EXPECT_TRUE(m == m2);
  EXPECT_TRUE(*query.expr == *query2.expr);
}

TEST(SolverTest, SharedMemAnswer) {
  // Mimic an answer
  ArrayCache cache;
  std::vector<std::vector<unsigned char> > array, array_res;
  array.push_back({1, 2, 3, 4, 5});
  array.push_back({6, 7, 8, 9, 10});

  SolverImpl::SolverRunStatus status = SolverImpl::SOLVER_RUN_STATUS_TIMEOUT,
                              status_res;

  bool success = true, success_res;
  bool hasSolution = true, hasSolution_res;

  SharedMem sm(SharedMem::defaultSize);
  SharedMem sm2(SharedMem::defaultSize);
  Serializer ser(sm);
  Deserializer deser(sm2, &cache);

  ser.serializeComputeInitialValuesAnswer(array, success, hasSolution, status);
  deser.deserializeComputeInitialValuesAnswer(array_res, success_res,
                                              hasSolution_res, status_res);

  EXPECT_TRUE(array == array_res);
  EXPECT_TRUE(success == success_res);
  EXPECT_TRUE(status == status_res);
  EXPECT_TRUE(hasSolution == hasSolution_res);
}

TEST(SolverTest, SharedMemFork) {

  auto pid = fork();

  if (pid == 0) {
    // child
    SharedMem sm_server(SharedMem::defaultSize,
                        "klee_" + std::to_string(getppid()));

    sm_server.lock();
    *((uint64_t *)sm_server.getAddr()) = 42;

    sm_server.signal(SharedMem::CONSUMER);
    sm_server.wait(SharedMem::PRODUCER);

    *((uint64_t *)sm_server.getAddr()) = 84;
    sm_server.unlock();
    sm_server.signal(SharedMem::CONSUMER);
  } else {
    SharedMem sm_client(SharedMem::defaultSize);

    sm_client.lock();
    sm_client.wait(SharedMem::CONSUMER);

    EXPECT_TRUE(*((uint64_t *)sm_client.getAddr()) == 42);

    sm_client.signal(SharedMem::PRODUCER);
    sm_client.wait(SharedMem::CONSUMER);

    EXPECT_TRUE(*((uint64_t *)sm_client.getAddr()) == 84);
    sm_client.unlock();
  }
}

TEST(SolverTest, Roundtrip) {
  ArrayCache cache;
  SharedMem sm_client(SharedMem::defaultSize);
  SharedMem sm_server(SharedMem::defaultSize);

  auto ar = cache.CreateArray("foo", 32);
  auto ul = UpdateList(ar, nullptr);

  ConstraintManager m;
  m.addConstraint(ReadExpr::create(ul, getConstant(0, 32)));
  m.addConstraint(ReadExpr::create(ul, getConstant(1, 32)));
  Query query(m, getConstant(3, 32), nullptr);

  Serializer ser_c(sm_client);
  std::vector<const Array *> empty;
  ser_c.serializeQuery(query, empty);

  Deserializer deser_s(sm_server, &cache);
  ConstraintManager m2;
  auto query2 = deser_s.deserializeQuery(m2);

  EXPECT_TRUE(m == m2);
  EXPECT_TRUE(*query.expr == *query2.expr);

  // Mimic an answer, written back from the server
  std::vector<std::vector<unsigned char> > array, array_res;
  array.push_back({1, 2, 3, 4, 5});
  array.push_back({6, 7, 8, 9, 10});

  SolverImpl::SolverRunStatus status = SolverImpl::SOLVER_RUN_STATUS_TIMEOUT,
                              status_res;

  bool success = true, success_res;
  bool hasSolution = true, hasSolution_res;

  Serializer ser_s(sm_server);
  Deserializer deser_c(sm_client, &cache);

  ser_s.serializeComputeInitialValuesAnswer(array, success, hasSolution,
                                            status);
  deser_c.deserializeComputeInitialValuesAnswer(array_res, success_res,
                                                hasSolution_res, status_res);

  EXPECT_TRUE(array == array_res);
  EXPECT_TRUE(success == success_res);
  EXPECT_TRUE(status == status_res);
  EXPECT_TRUE(hasSolution == hasSolution_res);
}
}
