//===-- Serialization.h -----------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_SERIALIZATION_H
#define KLEE_SERIALIZATION_H

#include "klee/SolverImpl.h"
#include <kj/array.h>
#include <capnp/common.h>
#include <memory>

namespace klee {
class Array;
class Expr;
class SharedMem;
class ArrayCache;
struct Query;

class SD {
protected:
  SharedMem &memObj;

public:
  SD(SharedMem &_memobj) : memObj(_memobj) {}
};

class Serializer : public SD {
public:
  Serializer(SharedMem &_memobj) : SD(_memobj) {}
  void serializeExpression(const ref<Expr> &e, bool success);
  void serializeQuery(const Query &query,
                      const std::vector<const Array *> &arrays);
  void serializeConstraintLogAnswer(char *str);
  void serializeComputeTruthAnswer(bool isValid, bool success);
  void serializeComputeInitialValuesAnswer(
      std::vector<std::vector<unsigned char> > &values, bool success,
      bool hasSolution, SolverImpl::SolverRunStatus runStatusCode);
  void serializeComputeValueAnswer(const ref<Expr> &expr, bool success);
};

class Deserializer : public SD {
private:
  ArrayCache *arrayCache;

public:
  Deserializer(SharedMem &_memobj, ArrayCache *_arrayCache)
      : SD(_memobj), arrayCache(_arrayCache) {}
  ref<Expr> deserializeExpression(bool &success);
  Query deserializeQuery(ConstraintManager &m);
  Query deserializeQuery(ConstraintManager &m,
                         std::vector<const Array *> &arrays);
  char *deserializeConstraintLogAnswer();
  void deserializeComputeTruthAnswer(bool &isValid, bool &success);
  void deserializeComputeInitialValuesAnswer(
      std::vector<std::vector<unsigned char> > &values, bool &success,
      bool &hasSolution, SolverImpl::SolverRunStatus &runStatusCode);
  void deserializeComputeValueAnswer(ref<Expr> &expr, bool &success);
};

kj::Array<capnp::word> serializeExpression(const ref<Expr> &e);
ref<Expr> deserializeExpression(kj::Array<capnp::word> &messageBuffer,
                                ArrayCache *arrayCache);

kj::Array<capnp::word> serializeQuery(const Query &query,
                                      const std::vector<const Array *> &arrays);

/// Deserializes query
/// We have to provide the constraintmanager, as it is typically a reference
/// from inside
/// a state
Query deserializeQuery(kj::Array<capnp::word> &messageBuffer,
                       ConstraintManager &m, ArrayCache *arrayCache);
}

#endif
