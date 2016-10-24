//===-- CachingSolver.cpp - Caching expression solver ---------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//


#include "klee/Solver.h"

#include "klee/Constraints.h"
#include "klee/Expr.h"
#include "klee/IncompleteSolver.h"
#include "klee/SolverImpl.h"

#include "klee/SolverStats.h"
#include "klee/ExecutionState.h"
#include "klee/TimerStatIncrementer.h"

#include "../Core/Executor.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"

#include "klee/Internal/Support/ErrorHandling.h"

#include <ciso646>

#ifdef _LIBCPP_VERSION
#include <unordered_map>
#define unordered_map std::unordered_map
#else
#include <tr1/unordered_map>
#define unordered_map std::tr1::unordered_map
#endif
#include <vector>

namespace klee {
	class KInstruction;

class CachingSolver : public SolverImpl {
private:
  const Executor* executor;

  ref<Expr> canonicalizeQuery(ref<Expr> originalQuery,
                              bool &negationUsed);

  void cacheInsert(const Query& query,
                   IncompleteSolver::PartialValidity result);

  bool cacheLookup(const Query& query,
                   IncompleteSolver::PartialValidity &result);
  
  struct CacheEntry {
    CacheEntry(const ConstraintSetView &c, ref<Expr> q)
        : constraints(c.begin(), c.end()), query(q) {}

    CacheEntry(const CacheEntry &ce)
      : constraints(ce.constraints), query(ce.query) {}

    std::vector<ref<Expr> > constraints;
    ref<Expr> query;

    bool operator==(const CacheEntry &b) const {
      return constraints==b.constraints && *query.get()==*b.query.get();
    }

  };
  
  struct CacheEntryHash {
    unsigned operator()(const CacheEntry &ce) const {
      unsigned result = ce.query->hash();

      for (auto it = ce.constraints.begin(); it != ce.constraints.end(); ++it)
        result ^= (*it)->hash();
      
      return result;
    }
  };

  typedef unordered_map<CacheEntry, 
                        IncompleteSolver::PartialValidity, 
                        CacheEntryHash> cache_map;
  typedef std::pair<const CacheEntry, IncompleteSolver::PartialValidity> CacheItem;

  Solver *solver;
  cache_map cache;

  typedef std::pair<const KInstruction*, const CacheItem*> QOCacheItem;

  static inline bool qOCacheItemCompare_Lower(const QOCacheItem& it, const KInstruction* val){
      return it.first < val;
  }

  static inline bool qOCacheItemCompare_Upper(const KInstruction* val, const QOCacheItem& it){
      return val < it.first;
  }

  std::vector<QOCacheItem> queryOriginCache;

public:
  CachingSolver(Solver *s, const Executor* _executor) : executor(_executor), solver(s){}
  ~CachingSolver() { cache.clear(); delete solver; }

  bool computeValidity(const Query&, Solver::Validity &result);
  bool computeTruth(const Query&, bool &isValid);
  bool computeValue(const Query& query, ref<Expr> &result) {
    ++stats::queryCacheMisses;
    return solver->impl->computeValue(query, result);
  }
  bool computeInitialValues(const Query& query,
                            const std::vector<const Array*> &objects,
                            std::vector< std::vector<unsigned char> > &values,
                            bool &hasSolution) {
    ++stats::queryCacheMisses;
    return solver->impl->computeInitialValues(query, objects, values, 
                                              hasSolution);
  }
  SolverRunStatus getOperationStatusCode();
  char *getConstraintLog(const Query&);
  void setCoreSolverTimeout(double timeout);

  void setIncrementalStatus(bool enable) {
    solver->impl->setIncrementalStatus(enable);
  }

  bool getIncrementalStatus() { return solver->impl->getIncrementalStatus(); }

  void clearSolverStack() { solver->impl->clearSolverStack(); }
};

/** @returns the canonical version of the given query.  The reference
    negationUsed is set to true if the original query was negated in
    the canonicalization process. */
ref<Expr> CachingSolver::canonicalizeQuery(ref<Expr> originalQuery,
                                           bool &negationUsed) {
  ref<Expr> negatedQuery = Expr::createIsZero(originalQuery);

  // select the "smaller" query to the be canonical representation
  if (originalQuery.compare(negatedQuery) < 0) {
    negationUsed = false;
    return originalQuery;
  } else {
    negationUsed = true;
    return negatedQuery;
  }
}

/** @returns true on a cache hit, false of a cache miss.  Reference
    value result only valid on a cache hit. */
bool CachingSolver::cacheLookup(const Query& query,
                                IncompleteSolver::PartialValidity &result) {
  bool negationUsed;
  ref<Expr> canonicalQuery = canonicalizeQuery(query.expr, negationUsed);
  const CacheEntry ce(query.constraints, canonicalQuery);

  { //QueryOriginCache
      TimerStatIncrementer t(stats::queryOriginTime);
      //get current code position
      if (query.queryOrigin and query.queryOrigin->prevPC){
          KInstruction* codeposition = query.queryOrigin->prevPC;
          //lookup query origin cache
          auto qit = std::lower_bound(queryOriginCache.begin(), queryOriginCache.end(), codeposition, qOCacheItemCompare_Lower);
          //search all cache entries for this code position
          while (qit != queryOriginCache.end() and qit->first == codeposition){
              if (qit->second->first == ce){
                  ++stats::queryOriginCacheHits;
                  result = (negationUsed ?
                            IncompleteSolver::negatePartialValidity(qit->second->second) :
                            qit->second->second);
                  return true;
              }
              qit++;
          }
      }
  }

  cache_map::iterator it = cache.find(ce);
  
  if (it != cache.end()) {
    result = (negationUsed ?
              IncompleteSolver::negatePartialValidity(it->second) :
              it->second);
    return true;
  }
  
  return false;
}

/// Inserts the given query, result pair into the cache.
void CachingSolver::cacheInsert(const Query& query,
                                IncompleteSolver::PartialValidity result) {
  bool negationUsed;
  ref<Expr> canonicalQuery = canonicalizeQuery(query.expr, negationUsed);

  CacheEntry ce(query.constraints, canonicalQuery);
  IncompleteSolver::PartialValidity cachedResult = 
    (negationUsed ? IncompleteSolver::negatePartialValidity(result) : result);
  std::pair<cache_map::iterator, bool> itpair = cache.insert(std::make_pair(ce, cachedResult));

  if (itpair.second){ //QueryOriginCache
      TimerStatIncrementer t(stats::queryOriginTime);
      //get current code position
      if (query.queryOrigin and query.queryOrigin->prevPC){
          if (queryOriginCache.size() == 0 ){
            assert(executor != nullptr and executor->kmodule != 0);
            queryOriginCache.resize(executor->kmodule->infos->getMaxID());
            llvm::errs() << "Resized QueryOriginCache to " << queryOriginCache.size() << "\n";
          }
          const KInstruction* codeposition = query.queryOrigin->prevPC;
          auto qit = std::upper_bound(queryOriginCache.begin(), queryOriginCache.end(), codeposition, qOCacheItemCompare_Upper);
          queryOriginCache.insert(qit, std::make_pair(codeposition, &*itpair.first));
      }
  }
}

bool CachingSolver::computeValidity(const Query& query,
                                    Solver::Validity &result) {
  IncompleteSolver::PartialValidity cachedResult;
  bool tmp, cacheHit = cacheLookup(query, cachedResult);
  
  if (cacheHit) {
    switch(cachedResult) {
    case IncompleteSolver::MustBeTrue:   
      result = Solver::True;
      ++stats::queryCacheHits;
      return true;
    case IncompleteSolver::MustBeFalse:  
      result = Solver::False;
      ++stats::queryCacheHits;
      return true;
    case IncompleteSolver::TrueOrFalse:  
      result = Solver::Unknown;
      ++stats::queryCacheHits;
      return true;
    case IncompleteSolver::MayBeTrue: {
      ++stats::queryCacheMisses;
      if (!solver->impl->computeTruth(query, tmp))
        return false;
      ++stats::queryOriginCacheReplace;
      if (tmp) {
        cacheInsert(query, IncompleteSolver::MustBeTrue);
        result = Solver::True;
        return true;
      } else {
        cacheInsert(query, IncompleteSolver::TrueOrFalse);
        result = Solver::Unknown;
        return true;
      }
    }
    case IncompleteSolver::MayBeFalse: {
      ++stats::queryCacheMisses;
      if (!solver->impl->computeTruth(query.negateExpr(), tmp))
        return false;
      ++stats::queryOriginCacheReplace;
      if (tmp) {
        cacheInsert(query, IncompleteSolver::MustBeFalse);
        result = Solver::False;
        return true;
      } else {
        cacheInsert(query, IncompleteSolver::TrueOrFalse);
        result = Solver::Unknown;
        return true;
      }
    }
    default: assert(0 && "unreachable");
    }
  }

  ++stats::queryCacheMisses;
  
  if (!solver->impl->computeValidity(query, result))
    return false;

  switch (result) {
  case Solver::True: 
    cachedResult = IncompleteSolver::MustBeTrue; break;
  case Solver::False: 
    cachedResult = IncompleteSolver::MustBeFalse; break;
  default: 
    cachedResult = IncompleteSolver::TrueOrFalse; break;
  }
  
  cacheInsert(query, cachedResult);
  return true;
}

bool CachingSolver::computeTruth(const Query& query,
                                 bool &isValid) {
  IncompleteSolver::PartialValidity cachedResult;
  bool cacheHit = cacheLookup(query, cachedResult);

  // a cached result of MayBeTrue forces us to check whether
  // a False assignment exists.
  if (cacheHit && cachedResult != IncompleteSolver::MayBeTrue) {
    ++stats::queryCacheHits;
    isValid = (cachedResult == IncompleteSolver::MustBeTrue);
    return true;
  }

  ++stats::queryCacheMisses;
  
  // cache miss: query solver
  if (!solver->impl->computeTruth(query, isValid))
    return false;

  if (isValid) {
    cachedResult = IncompleteSolver::MustBeTrue;
  } else if (cacheHit) {
    // We know a true assignment exists, and query isn't valid, so
    // must be TrueOrFalse.
    assert(cachedResult == IncompleteSolver::MayBeTrue);
    cachedResult = IncompleteSolver::TrueOrFalse;
  } else {
    cachedResult = IncompleteSolver::MayBeFalse;
  }
  
  if (cacheHit)
      ++stats::queryOriginCacheReplace;

  cacheInsert(query, cachedResult);
  return true;
}

SolverImpl::SolverRunStatus CachingSolver::getOperationStatusCode() {
  return solver->impl->getOperationStatusCode();
}

char *CachingSolver::getConstraintLog(const Query& query) {
  return solver->impl->getConstraintLog(query);
}

void CachingSolver::setCoreSolverTimeout(double timeout) {
  solver->impl->setCoreSolverTimeout(timeout);
}

///
Solver* createCachingSolver(Solver *_solver, const Executor* executor) {
  return new Solver(new CachingSolver(_solver, executor));
}

}
