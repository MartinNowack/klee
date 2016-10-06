//===-- SolverStats.h -------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_SOLVERSTATS_H
#define KLEE_SOLVERSTATS_H

#include "klee/Statistic.h"

namespace klee {
namespace stats {

  extern Statistic cexCacheTime;
  extern Statistic queries;
  extern Statistic queriesInvalid;
  extern Statistic queriesValid;
  extern Statistic queryCacheHits;
  extern Statistic queryCacheMisses;
  extern Statistic queryCexCacheHits;
  extern Statistic queryCexCacheMisses;
  extern Statistic queryConstructTime;
  extern Statistic queryConstructs;
  extern Statistic queryCounterexamples;
  extern Statistic queryTime;
  extern Statistic indepConstraintsTime;
  extern Statistic serializerTime;
  extern Statistic addConstraintTime;
  
  extern Statistic queryIncremental;
  extern Statistic queryIncCalculationTime;
#ifdef DEBUG
  extern Statistic arrayHashTime;
#endif

  extern Statistic queryOriginCacheHits;
  extern Statistic queryOriginTime;

}
}

#endif
