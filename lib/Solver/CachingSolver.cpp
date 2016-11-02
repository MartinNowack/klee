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
#include <memory>

namespace klee {
	class KInstruction;

class CachingSolver : public SolverImpl {
private:

  Solver *solver;

  //ORIGIN SOURCE
  const Executor* executor;

  //CACHE
  struct CacheKey {
    private:
      const std::vector<ref<Expr> > constraints;
      const ref<Expr> query;
      mutable unsigned hash;

    public:
      CacheKey(const ConstraintSetView &c, ref<Expr> q)
        : constraints(c.begin(), c.end()), query(q), hash(0) {}

      CacheKey(const CacheKey &ce)
        : constraints(ce.constraints), query(ce.query), hash(0) {}

      bool operator==(const CacheKey &b) const {
        if (hash != 0)
          return hash==b.get_hash() && constraints==b.constraints && *query.get()==*b.query.get();
        else
          return constraints==b.constraints && *query.get()==*b.query.get();
      }

      const unsigned& get_hash() const{
        if (hash == 0){
          hash = query->hash();
          for (auto it = constraints.begin(); it != constraints.end(); ++it)
            hash ^= (*it)->hash();
        }
        return hash;
      }

  };
  
  struct CacheKeyHash {
    const unsigned& operator()(const std::shared_ptr<CacheKey> &ce) const {
      return ce->get_hash();
    }
  };

  struct CacheKeyCmp {
      unsigned operator()(const std::shared_ptr<CacheKey> ce, const std::shared_ptr<CacheKey> oce) const {
        return (*ce) == (*oce);
      }
  };

  typedef std::vector<IncompleteSolver::PartialValidity> CacheStorage;
  CacheStorage cacheStorage;

  //SIMPLE CACHE
  typedef unordered_map<const std::shared_ptr<CacheKey>,
                        const CacheStorage::size_type,
                        CacheKeyHash,
                        CacheKeyCmp> SimpleCache;

  SimpleCache cache;

  //QUERY ORIGIN CACHE

  typedef SimpleCache QOCacheItem;
  typedef std::vector<QOCacheItem*> QOCache;

  QOCache queryOriginCache;
  QOCache::size_type qoc_size;

private:
  ref<Expr> canonicalizeQuery(ref<Expr> originalQuery,
                              bool &negationUsed);

  void cacheInsert(const Query& query,
                   IncompleteSolver::PartialValidity result,
                   CacheStorage::size_type cacheHitAt);

  CacheStorage::size_type cacheLookup(const Query& query,
                   IncompleteSolver::PartialValidity &result);

public:
  CachingSolver(Solver *s, const Executor* _executor) : solver(s), executor(_executor), qoc_size(0){
    // insert sentinel cache entry at index 0 meaning cache miss
    cacheStorage.push_back(IncompleteSolver::PartialValidity::None);
  }
  ~CachingSolver() {
    for(auto it=queryOriginCache.begin(); it != queryOriginCache.end(); it++){
      if(*it){
        (*it)->clear();
        delete (*it);
      }
    }
    queryOriginCache.clear();
    cache.clear();
    cacheStorage.clear();
    delete solver;
  }

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
CachingSolver::CacheStorage::size_type CachingSolver::cacheLookup(const Query& query,
                                IncompleteSolver::PartialValidity &result) {
  bool negationUsed;
  ref<Expr> canonicalQuery = canonicalizeQuery(query.expr, negationUsed);
  const std::shared_ptr<CacheKey> ce = std::make_shared<CacheKey>(query.constraints, canonicalQuery);

  { //QueryOriginCache
    TimerStatIncrementer t(stats::queryOriginTime);
    if ( qoc_size != 0 ){
      //get current code position
      if (query.queryOrigin and query.queryOrigin->prevPC){
      //lookup query origin cache
        const QOCacheItem* qit =
            queryOriginCache[query.queryOrigin->prevPC->info->id];
        if ( qit != nullptr ){
          //search all cache entries for this code position
          QOCacheItem::const_iterator qocit = qit->find(ce);
          if (qocit != qit->end()) {
            ++stats::queryOriginCacheHits;
            result = (negationUsed ?
                      IncompleteSolver::negatePartialValidity(cacheStorage[qocit->second]) :
                      cacheStorage[qocit->second]);
            return qocit->second;
          }
        }
      }
    }
  }


  SimpleCache::iterator it = cache.find(ce);
  
  if (it != cache.end()) {
    result = (negationUsed ?
              IncompleteSolver::negatePartialValidity(cacheStorage[it->second]) :
              cacheStorage[it->second]);
    return it->second;
  }
  
  return 0;
}

/// Inserts the given query, result pair into the cache.
void CachingSolver::cacheInsert(const Query& query,
                                IncompleteSolver::PartialValidity result,
                                CacheStorage::size_type cacheHitAt) {
  bool negationUsed;
  ref<Expr> canonicalQuery = canonicalizeQuery(query.expr, negationUsed);

  IncompleteSolver::PartialValidity cachedResult = 
    (negationUsed ? IncompleteSolver::negatePartialValidity(result) : result);

  // cacheHitAt index 0 means "miss" (see sentinel cache entry in constructor
  if (cacheHitAt > 0){
    // possibly improved the solution (e.g. STP-Solution instead of CexCache-Solution)
    cacheStorage[cacheHitAt] = cachedResult; // no nead to touch the caches here!
    ++stats::queryOriginCacheReplace;
  }else{
    const std::shared_ptr<CacheKey> ce =
        std::make_shared<CacheKey>(query.constraints, canonicalQuery);

    std::pair<SimpleCache::iterator, bool> itpair =
        cache.insert(std::make_pair(ce, cacheStorage.size()));

    assert(itpair.second && "with cacheHitAt == 0 we assume the cache entry not to be in the cache yet!");

    cacheStorage.push_back(cachedResult);
    //QueryOriginCache
    TimerStatIncrementer t(stats::queryOriginTime);
    //make sure the query origin is accessible
    if (query.queryOrigin and query.queryOrigin->prevPC){
        if (qoc_size == 0){
          // preallocate the QueryOriginCache to match
          // the total number of Instructions
          assert(executor != nullptr and executor->kmodule != 0);
          queryOriginCache.resize(
              executor->kmodule->infos->getMaxID(),
              nullptr
          );
          // mark preallocation done for fast access
          qoc_size = queryOriginCache.size();
          assert(qoc_size != 0 && "QueryOriginCache size should be > 0");
          llvm::errs()
              << "Resized QueryOriginCache to "
              << qoc_size << "\n";
        }
        // the instruction-ID is used as the queries origin
        const QOCache::size_type& codelocation =
            query.queryOrigin->prevPC->info->id;
        // we still see a multiple queries from the same code location
        QOCacheItem* qit = queryOriginCache[codelocation];
        if (qit == nullptr){ // this code location sees its first query here
          qit = new QOCacheItem();
          queryOriginCache[codelocation] = qit;
        }
        qit->insert(std::make_pair(ce,itpair.first->second));
    }
  }
}

bool CachingSolver::computeValidity(const Query& query,
                                    Solver::Validity &result) {
  IncompleteSolver::PartialValidity cachedResult;
  CacheStorage::size_type cacheHitAt = cacheLookup(query, cachedResult);
  bool cacheHit = cacheHitAt > 0;
  
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
      if (!solver->impl->computeTruth(query, cacheHit))
        return false;
      if (cacheHit) {
        cacheInsert(query, IncompleteSolver::MustBeTrue, cacheHitAt);
        result = Solver::True;
        return true;
      } else {
        cacheInsert(query, IncompleteSolver::TrueOrFalse, cacheHitAt);
        result = Solver::Unknown;
        return true;
      }
    }
    case IncompleteSolver::MayBeFalse: {
      ++stats::queryCacheMisses;
      if (!solver->impl->computeTruth(query.negateExpr(), cacheHit))
        return false;
      if (cacheHit) {
        cacheInsert(query, IncompleteSolver::MustBeFalse, cacheHitAt);
        result = Solver::False;
        return true;
      } else {
        cacheInsert(query, IncompleteSolver::TrueOrFalse, cacheHitAt);
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
  
  cacheInsert(query, cachedResult, cacheHitAt);
  return true;
}

bool CachingSolver::computeTruth(const Query& query,
                                 bool &isValid) {
  IncompleteSolver::PartialValidity cachedResult;
  CacheStorage::size_type cacheHitAt = cacheLookup(query, cachedResult);
  bool cacheHit = cacheHitAt > 0;

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
  
  cacheInsert(query, cachedResult, cacheHitAt);
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
