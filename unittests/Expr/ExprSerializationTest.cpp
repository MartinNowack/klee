/*
 * ExprSerializationTest.cpp
 *
 * Author: Martin Nowack
 */

#include "gtest/gtest.h"

#include "klee/Expr.h"
#include "klee/Constraints.h"
#include "klee/Solver.h"
#include "klee/util/ArrayCache.h"
#include "klee/util/Serialization.h"

using namespace klee;

ref<ConstantExpr> getConstant(int value, Expr::Width width) {
  int64_t ext = value;
  uint64_t trunc = ext & (((uint64_t)-1LL) >> (64 - width));
  return ConstantExpr::create(trunc, width);
}

TEST(ExprSerialization, BasicConstruction) {
  ArrayCache cache;
  auto exp1 = getConstant(42, 32);

  auto s1 = serializeExpression(exp1);
  EXPECT_TRUE(*exp1 == *deserializeExpression(s1, &cache));

  auto exp2 = AddExpr::create(exp1, exp1);
  auto s2 = serializeExpression(exp2);
  EXPECT_TRUE(*exp2 == *deserializeExpression(s2, &cache));
}

TEST(ExprSerialization, ReadArray) {
  ArrayCache cache;

  auto ar = cache.CreateArray("foo", 32);
  auto ul = UpdateList(ar, nullptr);
  auto re = ReadExpr::create(ul, getConstant(0, 32));

  auto s = serializeExpression(re);
  auto d = deserializeExpression(s, &cache);
  EXPECT_TRUE(*re == *d);
}

TEST(ExprSerialization, ReadArrayConcrete) {
  ArrayCache cache;
  std::vector<ref<ConstantExpr> > values;
  for (size_t i = 0, j = 5; i != j; ++i) {
    values.emplace_back(getConstant(i, 8));
  }
  auto ar = cache.CreateArray("foo", values.size(), &values[0],
                              &values[0] + values.size());
  auto ul = UpdateList(ar, nullptr);
  auto re = ReadExpr::create(ul, getConstant(0, 32));

  auto s = serializeExpression(re);
  auto d = deserializeExpression(s, &cache);

  auto re2 = dyn_cast<ReadExpr>(d);

  for (size_t i = 0, j = ar->constantValues.size(); i != j; ++i) {
    EXPECT_TRUE(*re2->updates.root->constantValues[i] ==
                *ar->constantValues[i]);
  }
}

TEST(ExprSerialization, ReadArraySymbolic) {
  ArrayCache cache;
  std::vector<ref<ConstantExpr> > values;
  auto ar = cache.CreateArray("foo", values.size(), &values[0],
                              &values[0] + values.size());

  EXPECT_TRUE(ar->isSymbolicArray());

  auto un3 = new UpdateNode(nullptr, getConstant(1, 32), getConstant(2, 8));
  auto un2 = new UpdateNode(un3, getConstant(1, 32), getConstant(41, 8));
  auto un = new UpdateNode(un2, getConstant(1, 32), getConstant(41, 8));

  auto ul = UpdateList(ar, un);
  auto ul2 = UpdateList(ar, un2);

  ul.extend(getConstant(1, 32), getConstant(2, 8));
  ul.extend(getConstant(1, 32), getConstant(42, 8));
  ul.extend(getConstant(1, 32), getConstant(84, 8));
  ul.extend(getConstant(1, 32), getConstant(2, 8));

  ul2.extend(getConstant(1, 32), getConstant(84, 8));
  ul2.extend(getConstant(1, 32), getConstant(2, 8));
  ul2.extend(getConstant(1, 32), getConstant(42, 8));
  ul2.extend(getConstant(1, 32), getConstant(2, 8));

  auto re = ReadExpr::create(ul, getConstant(0, 32));
  auto re2 = ReadExpr::create(ul2, getConstant(0, 32));
  auto a_e = AndExpr::create(re, re2);

  auto s = serializeExpression(a_e);
  auto d = deserializeExpression(s, &cache);

  // Patch array as they are not the the same object
  auto a_des = dyn_cast<AndExpr>(d);
  dyn_cast<ReadExpr>(a_des->left)->updates.root = ar;
  dyn_cast<ReadExpr>(a_des->right)->updates.root = ar;

  EXPECT_TRUE(*a_e == *a_des);
}

TEST(ExprSerialization, SelectExpr) {
  ArrayCache cache;
  auto ar = cache.CreateArray("foo", 32);
  auto ul = UpdateList(ar, nullptr);
  auto re = ReadExpr::create(ul, getConstant(0, 32));

  auto eq = EqExpr::create(re, getConstant(1, 8));

  auto seE = SelectExpr::create(eq, getConstant(42, 32), getConstant(43, 32));

  auto s = serializeExpression(seE);
  auto d = deserializeExpression(s, &cache);

  EXPECT_TRUE(*seE == *d);
}

TEST(ExprSerialization, ExtractExpr) {
  ArrayCache cache;
  auto ar = cache.CreateArray("arr1", 32);
  auto ul = UpdateList(ar, nullptr);
  auto re = ReadExpr::create(ul, getConstant(0, 32));

  auto ee = ExtractExpr::create(re, 0, Expr::Int8);
  auto s = serializeExpression(ee);
  auto d = deserializeExpression(s, &cache);
  EXPECT_TRUE(*ee == *d);

  ee = ExtractExpr::create(re, 0, Expr::Bool);
  s = serializeExpression(ee);
  d = deserializeExpression(s, &cache);
  EXPECT_TRUE(*ee == *d);
}

#define TestBinary(name)                                                       \
  TEST(ExprSerialization, name##Expr) {                                        \
    ArrayCache cache;                                                          \
    auto ar = cache.CreateArray("foo", 32);                                    \
    auto ul = UpdateList(ar, nullptr);                                         \
    auto re = ReadExpr::create(ul, getConstant(1, 32));                        \
    auto exp1 = getConstant(42, 8);                                            \
    auto exp2 = name##Expr::create(re, exp1);                                  \
    auto s = serializeExpression(exp2);                                        \
    auto d = deserializeExpression(s, &cache);                                 \
    EXPECT_TRUE(*d == *exp2);                                                  \
  }

#define TestUnary(name)                                                        \
  TEST(ExprSerialization, name##Expr) {                                        \
    ArrayCache cache;                                                          \
    auto ar = cache.CreateArray("foo", 32);                                    \
    auto ul = UpdateList(ar, nullptr);                                         \
    auto re = ReadExpr::create(ul, getConstant(1, 32));                        \
    auto exp = name##Expr::create(re);                                         \
    auto s = serializeExpression(exp);                                         \
    auto d = deserializeExpression(s, &cache);                                 \
    EXPECT_TRUE(*d == *exp);                                                   \
  }

#define TestUnarySize(name)                                                    \
  TEST(ExprSerialization, name##Expr) {                                        \
    ArrayCache cache;                                                          \
    auto ar = cache.CreateArray("foo", 32);                                    \
    auto ul = UpdateList(ar, nullptr);                                         \
    auto re = ReadExpr::create(ul, getConstant(1, 32));                        \
    auto exp = name##Expr::create(re, 64);                                     \
    auto s = serializeExpression(exp);                                         \
    auto d = deserializeExpression(s, &cache);                                 \
    EXPECT_TRUE(*d == *exp);                                                   \
  }
// For testing purposes
TestUnary(NotOptimized)

TestBinary(Concat)

TestUnarySize(ZExt)
TestUnarySize(SExt)


TestBinary(Add)
TestBinary(Sub)
TestBinary(Mul)
TestBinary(SDiv)
TestBinary(UDiv)
TestBinary(URem)
TestBinary(SRem)

// Bit
TestUnary(Not)
TestBinary(And)
TestBinary(Or)
TestBinary(Xor)
TestBinary(Shl)
TestBinary(LShr)
TestBinary(AShr)

// Compare
TestBinary(Eq)
TestBinary(Ne) ///< Not used in canonical form

TestBinary(Ult)
TestBinary(Ule)

TestBinary(Ugt) ///< Not used in canonical form
TestBinary(Uge) ///< Not used in canonical form
TestBinary(Slt)
TestBinary(Sle)
TestBinary(Sgt) ///< Not used in canonical form
TestBinary(Sge) ///< Not used in canonical form

#undef TestBinary
#undef TestUnary

    TEST(ExprSerialization, Query) {
  ArrayCache cache;
  auto ar = cache.CreateArray("foo", 32);
  auto ul = UpdateList(ar, nullptr);

  ConstraintManager m;
  m.addConstraint(ReadExpr::create(ul, getConstant(0, 32)));
  m.addConstraint(ReadExpr::create(ul, getConstant(1, 32)));

  Query query(m, getConstant(3, 32));

  std::vector<const Array *> empty;
  auto s = serializeQuery(query, empty);

  ConstraintManager m2;
  auto query2 = deserializeQuery(s, m2, &cache);

  EXPECT_TRUE(m == m2);
  EXPECT_TRUE(*query.expr == *query2.expr);
}
