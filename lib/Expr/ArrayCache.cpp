#include "klee/util/ArrayCache.h"

namespace klee {

void ArrayCache::clear() {
  // Free Allocated Array objects
  for (ArrayHashMap::iterator ai = cachedSymbolicArrays.begin(), e =
      cachedSymbolicArrays.end(); ai != e; ++ai) {
    delete *ai;
  }
  for (ArrayPtrVec::iterator ai = concreteArrays.begin(), e =
      concreteArrays.end(); ai != e; ++ai) {
    delete *ai;
  }
  cachedSymbolicArrays.clear();
  concreteArrays.clear();
}

ArrayCache::~ArrayCache() {
  // Free Allocated Array objects
  clear();
}

uint64_t ArrayCache::getArrayUID(const Array *ar) const {
  return ar->uid;
}

const Array * ArrayCache::getArray(uint64_t uid) const {
  if (!uid || uid > concreteArrays.size())
	  return 0;
  return concreteArrays[uid-1];
}

const Array *
ArrayCache::CreateArray(const std::string &_name, uint64_t _size,
                        const ref<ConstantExpr> *constantValuesBegin,
                        const ref<ConstantExpr> *constantValuesEnd,
                        Expr::Width _domain, Expr::Width _range, uint64_t uid) {
  const Array *array = new Array(_name, _size, constantValuesBegin,
                                 constantValuesEnd, _domain, _range);
  if (array->isSymbolicArray()) {
    std::pair<ArrayHashMap::const_iterator, bool> success =
        cachedSymbolicArrays.insert(array);
    if (success.second) {
      // Cache miss
      return array;
    }
    // Cache hit
    delete array;
    array = *(success.first);
    assert(array->isSymbolicArray() &&
           "Cached symbolic array is no longer symbolic");
    return array;
  } else {
    assert(array->isConstantArray());
    // If no uid is given, we just append to the current array cache
    if (!uid) {
      // Treat every constant array as distinct so we never cache them
      concreteArrays.push_back(array); // For deletion later
      array->uid = concreteArrays.size() + 1;
      return array;
    } else {
      array->uid = uid;
      if (uid > concreteArrays.size())
        concreteArrays.resize(uid);
      concreteArrays[uid - 1] = array;
      return array;
    }
  }
}
}
