//===-- ArrayExprHash.h --------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef __UTIL_ARRAYEXPRHASH_H__
#define __UTIL_ARRAYEXPRHASH_H__

#include "klee/Expr.h"
#include "klee/TimerStatIncrementer.h"
#include "klee/SolverStats.h"

#include <map>

#include <ciso646>
#ifdef _LIBCPP_VERSION
#include <unordered_map>
#define unordered_map std::unordered_map
#else
#include <tr1/unordered_map>
#define unordered_map std::tr1::unordered_map
#endif

namespace klee {
  
struct ArrayHashFn  {
  unsigned operator()(const Array* array) const {
    return(array ? array->hash() : 0);
  }
};
    
struct ArrayCmpFn {
  bool operator()(const Array* array1, const Array* array2) const {
    return(array1 == array2);
  }
};  
  
struct UpdateNodeHashFn  {
  unsigned
  operator()(const std::pair<const UpdateNode *, const Array *> un_a) const {
    return (un_a.first && un_a.second ? un_a.first->hash() + un_a.second->hash()
                                      : 0);
  }
};
    
struct UpdateNodeCmpFn {
  bool
  operator()(const std::pair<const UpdateNode *, const Array *> un_a1,
             const std::pair<const UpdateNode *, const Array *> un_a2) const {
    return (un_a1.first == un_a2.first && un_a1.second == un_a2.second);
  }
};  

template<class T>
class ArrayExprHash {  
public:
  
  ArrayExprHash() {};
  // Note: Extend the class and overload the destructor if the objects of type T
  // that are to be hashed need to be explicitly destroyed
  // As an example, see class STPArrayExprHash
  virtual ~ArrayExprHash() {};
   
  bool lookupArrayExpr(const Array* array, T& exp) const;
  void hashArrayExpr(const Array* array, T& exp);

  bool lookupUpdateNodeExpr(const UpdateNode *un, const Array *array,
                            T &exp) const;
  void hashUpdateNodeExpr(const UpdateNode *un, const Array *array, T &exp);

protected:
  typedef unordered_map<const Array*, T, ArrayHashFn, ArrayCmpFn> ArrayHash;
  typedef typename ArrayHash::iterator ArrayHashIter;
  typedef typename ArrayHash::const_iterator ArrayHashConstIter;

  typedef unordered_map<std::pair<const UpdateNode *, const Array *>, T,
                        UpdateNodeHashFn, UpdateNodeCmpFn> UpdateNodeHash;
  typedef typename UpdateNodeHash::iterator UpdateNodeHashIter;
  typedef typename UpdateNodeHash::const_iterator UpdateNodeHashConstIter;
  
  ArrayHash      _array_hash;
  UpdateNodeHash _update_node_hash;  
};


template<class T>
bool ArrayExprHash<T>::lookupArrayExpr(const Array* array, T& exp) const {
  bool res = false;
  
#ifdef DEBUG
  TimerStatIncrementer t(stats::arrayHashTime);
#endif
  
  assert(array);  
  ArrayHashConstIter it = _array_hash.find(array);
  if (it != _array_hash.end()) {
    exp = it->second;
    res = true;
  }  
  return(res);  
}

template<class T>
void ArrayExprHash<T>::hashArrayExpr(const Array* array, T& exp) {
  
#ifdef DEBUG  
   TimerStatIncrementer t(stats::arrayHashTime);
#endif
   
   assert(array);
  _array_hash[array] = exp;
}

template <class T>
bool ArrayExprHash<T>::lookupUpdateNodeExpr(const UpdateNode *un,
                                            const Array *array, T &exp) const {
  bool res = false;
  
#ifdef DEBUG
  TimerStatIncrementer t(stats::arrayHashTime);
#endif
  
  assert(un);
  UpdateNodeHashConstIter it =
      _update_node_hash.find(std::make_pair(un, array));
  if (it != _update_node_hash.end()) {
    exp = it->second;
    res = true;
  }  
  return(res);   
}

template <class T>
void ArrayExprHash<T>::hashUpdateNodeExpr(const UpdateNode *un,
                                          const Array *array, T &exp) {
#ifdef DEBUG
  TimerStatIncrementer t(stats::arrayHashTime);
#endif

  assert(un && array);
  _update_node_hash[std::make_pair(un, array)] = exp;
}

}

#undef unordered_map
#undef unordered_set

#endif
