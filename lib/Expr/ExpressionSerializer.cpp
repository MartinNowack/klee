/*
 * ExpressionSerializer.cpp
 *
 *  Created on: Aug 5, 2015
 *      Author: seadmin
 */
#include "klee/Constraints.h"
#include "klee/Expr.h"
#include "klee/Solver.h"
#include "klee/util/ArrayCache.h"
#include "klee/util/Serialization.h"
#include "klee/util/SharedMemory.h"

#include "Expressions.capnp.h"
#define NDBEGUG
#include <capnp/common.h>
#include <capnp/message.h>
#include <capnp/serialize.h>
#include <capnp/blob.h>

#include <stdlib.h>
#include <unordered_map>

namespace {
struct ExprHash {
  unsigned operator()(const klee::Expr *e) const { return e->hash(); }
};

struct ExprCmp {
  bool operator()(const klee::Expr *a, const klee::Expr *b) const {
    return *a == *b;
  }
};
}

namespace klee {

capnp::ReaderOptions getReaderOpts() {
  capnp::ReaderOptions opts;
  opts.traversalLimitInWords = SharedMem::defaultSize / sizeof(capnp::word);
  opts.nestingLimit = 1024;
  return opts;
}

template <class T> class ExpressionSerializer {
protected:
  uint32_t getArrayIndex(const Array &ar) {
    for (size_t i = 0, j = usedArrays.size(); i != j; ++i) {
      if (usedArrays[i]->size == ar.size && usedArrays[i]->name == ar.name)
        return i;
    }
    usedArrays.push_back(&ar);
    return usedArrays.size() - 1;
  }

public:
  void populateArray(const std::vector<const Array *> &array) {
    for (auto ar : array)
      getArrayIndex(*ar);
    unrequestedArrayIndex = array.size();
  }

  void buildArray() {
    auto alist = message->getRoot<T>().initArrays(usedArrays.size());

    for (size_t i = 0, j = usedArrays.size(); i != j; ++i) {
      auto &ar = *usedArrays[i];
      auto array_builder = alist[i];
      array_builder.setName(ar.name);
      array_builder.setSize(ar.size);
      array_builder.setDomain(ar.domain);
      array_builder.setRange(ar.range);
      array_builder.setUid(ar.uid);

      auto cv = array_builder.initConstantValue(ar.constantValues.size());

      // Read all constant values
      size_t index = 0;
      for (auto e : ar.constantValues) {
        visitConstant(e.get());
        cv.set(index, itemStack.back());
        itemStack.pop_back();
        ++index;
      }
    }
    buildUpdates();
  }

  void buildUpdates() {
    auto ul = message->getRoot<T>().initUpdates(usedUpdates.size());

    for (auto &up_entry : usedUpdates) {
      auto entryOrphan = std::move(std::get<1>(up_entry.second));
      auto entry = entryOrphan.get();
      entry.setNext(getUpdateIndex((up_entry.first)->next));
      entry.setSize(up_entry.first->getSize());
      entry.setHashValue(up_entry.first->hash());

      auto idx = std::get<0>(up_entry.second) - 1;

      ul[idx].adoptPtr(std::move(entryOrphan));
    }
  }

  void buildExpressions() {
    auto expressionList =
        message->getRoot<T>().initExpressions(usedExpressions.size());

    for (auto &item : usedExpressions) {
      expressionList[std::get<0>(item.second)].adoptPtr(
          std::move(std::get<1>(item.second)));
    }
  }

  void setSuccess(bool success) { message->getRoot<T>().setSuccess(success); }

protected:
  uint32_t getUpdateIndex(const UpdateNode *node) {
    // reserve 0 for nullptr value
    if (!node)
      return 0;
    auto item = usedUpdates.find(node);
    if (item != usedUpdates.end())
      return std::get<0>(item->second);

    auto orphUpdateNode = orphanage.newOrphan<serial::UpdateNode>();
    auto un = orphUpdateNode.get();

    auto index = usedUpdates.size() + 1;
    auto res = usedUpdates.insert(std::make_pair(
        node, std::make_tuple(index, std::move(orphUpdateNode))));
    assert(res.second);

    visit(node->index);
    un.setIndex(itemStack.back());
    itemStack.pop_back();

    visit(node->value);
    un.setValue(itemStack.back());
    itemStack.pop_back();

    return index;
  }

  serial::Expr::Builder getAndAddExpr(const Expr *e, uint32_t &index) {
    auto it = usedExpressions.find(e);
    if (it != usedExpressions.end()) {
      index = std::get<0>(it->second);
      return std::get<1>(it->second).get();
    }

    auto orphExpr = orphanage.newOrphan<serial::Expr>();
    auto res = orphExpr.get();
    index = usedExpressions.size();
    usedExpressions.insert(
        std::make_pair(e, std::make_tuple(index, std::move(orphExpr))));

    return res;
  }

  void visitRead(const ReadExpr &re) {
    uint32_t exp_idx;
    auto exp = getAndAddExpr(&re, exp_idx);

    auto re_exp = exp.initReadExpr();

    re_exp.setIndexExpr(itemStack.back());
    itemStack.pop_back();

    // Set Array
    auto array_idx = getArrayIndex(*re.updates.root);
    re_exp.setArrayIndex(array_idx);

    // Iterate through all update list elements
    for (auto c = re.updates.head; c; c = c->next) {
      getUpdateIndex(c);
    }

    re_exp.setUpdatesIndex(getUpdateIndex(re.updates.head));

    itemStack.push_back(exp_idx);
  }

  void visitExtract(const ExtractExpr &ee) {
    uint32_t exp_idx;
    auto exp = getAndAddExpr(&ee, exp_idx);
    auto exExp = exp.initExtractExpr();
    exExp.setOffset(ee.offset);
    exExp.setWidth(ee.width);
    exExp.setKid(itemStack.back());
    itemStack.pop_back();

    itemStack.push_back(exp_idx);
  }

#define naryVisitor(name, nr_kids)                                             \
  void visit##name(const name##Expr &ee) {                                     \
    uint32_t exp_idx;                                                          \
    auto exp = getAndAddExpr(&ee, exp_idx);                                    \
    auto name##_exp = exp.init##name##Expr();                                  \
    auto kids = name##_exp.initKids(nr_kids);                                  \
    /* Put serialization kids in reverse order on the stack*/                  \
    /* as the visitor is working on expression kids in order*/                 \
    for (size_t i = 0; i < nr_kids; ++i) {                                     \
      kids.set(nr_kids - i - 1, itemStack.back());                             \
      itemStack.pop_back();                                                    \
    }                                                                          \
    itemStack.push_back(exp_idx);                                              \
  }

#define unaryVisitor(name) naryVisitor(name, 1)
#define binaryVisitor(name) naryVisitor(name, 2)
#define ternaryVisitor(name) naryVisitor(name, 3)

#define unarySizeVisitor(name)                                                 \
  void visit##name(const name##Expr &e) {                                      \
    uint32_t exp_idx;                                                          \
    auto exp = getAndAddExpr(&e, exp_idx);                                     \
    auto name##_exp = exp.init##name##Expr();                                  \
    name##_exp.setWidth(e.getWidth());                                         \
    name##_exp.setKid(itemStack.back());                                       \
    itemStack.pop_back();                                                      \
    itemStack.push_back(exp_idx);                                              \
  }
  ternaryVisitor(Select);
  binaryVisitor(Concat);

  unarySizeVisitor(ZExt);
  unarySizeVisitor(SExt);

  binaryVisitor(Add);
  binaryVisitor(Sub);
  binaryVisitor(Mul);
  binaryVisitor(UDiv);
  binaryVisitor(SDiv);
  binaryVisitor(URem);
  binaryVisitor(SRem);

  unaryVisitor(Not);
  unaryVisitor(NotOptimized);

  binaryVisitor(And);
  binaryVisitor(Or);

  binaryVisitor(Xor);
  binaryVisitor(Shl);
  binaryVisitor(LShr);
  binaryVisitor(AShr);

  // Compare
  binaryVisitor(Eq);
  binaryVisitor(Ult);
  binaryVisitor(Ule);
  binaryVisitor(Slt);
  binaryVisitor(Sle);

#undef unaryVisitor
#undef naryVisitor
#undef binaryVisitor

  void visitNe(const NeExpr &) { assert(0 && "should not happen"); }

  void visitUgt(const UgtExpr &) { assert(0 && "should not happen"); }

  void visitUge(const UgeExpr &) { assert(0 && "should not happen"); }

  void visitSgt(const SgtExpr &) { assert(0 && "should not happen"); }

  void visitSge(const SgeExpr &) { assert(0 && "should not happen"); }

  void visitConstant(const ConstantExpr *e) {
    uint32_t exp_idx;
    auto exp = getAndAddExpr(e, exp_idx);
    auto numWords = e->getAPValue().getNumWords();
    if (numWords == 1) {
      auto co_exp = exp.initConstantExpr();
      co_exp.setValue(*e->getAPValue().getRawData());
      co_exp.setWidth(e->getWidth());
    } else {
      // Handle big numbers
      auto bco_exp = exp.initLargeConstantExpr();
      auto val_list = bco_exp.initValue(numWords);
      auto raw_ptr = e->getAPValue().getRawData();
      for (size_t i = 0; i < numWords; ++i, ++raw_ptr)
        val_list.set(i, *raw_ptr);
      bco_exp.setWidth(e->getWidth());
    }
    itemStack.push_back(exp_idx);
  }

  // Working Stack for expression indices
  std::vector<uint32_t> itemStack;

  // List of arrays used in expressions or which are requested.
  // This array is sorted in the way, that first elements
  // are requested arrays, later elements are additionally used
  // arrays in expression
  std::vector<const Array *> usedArrays;

  // Points to the first array not requested.
  uint64_t unrequestedArrayIndex;

  // List of all update nodes used inside the expression
  std::unordered_map<const UpdateNode *,
                     std::tuple<uint32_t, capnp::Orphan<serial::UpdateNode> > >
      usedUpdates;

  std::unordered_map<const Expr *,
                     std::tuple<uint32_t, capnp::Orphan<serial::Expr> >,
                     ExprHash, ExprCmp> usedExpressions;

public:
  kj::Array<capnp::word> serialize() {
    assert(itemStack.size() == 0 && "Stack still contains items to work on");
    return capnp::messageToFlatArray(*message);
  }

private:
  std::unique_ptr< ::capnp::MessageBuilder> message;

  ::capnp::Orphanage orphanage;

public:
  ExpressionSerializer()
      : unrequestedArrayIndex(0), message(new capnp::MallocMessageBuilder()),
        orphanage(
            capnp::Orphanage::getForMessageContaining(message->getRoot<T>())) {}

  ExpressionSerializer(SharedMem &memObj)
      : unrequestedArrayIndex(0), message(new capnp::MMapMessageBuilder(
                                      memObj.getAddr(), memObj.getSize())),
        orphanage(
            capnp::Orphanage::getForMessageContaining(message->getRoot<T>())) {}

  void visitQuery(const Query &query) {
    auto q = message->initRoot<T>();
    auto constraints = q.initConstraints(query.constraints.size());
    size_t cntr = 0;
    for (auto cons : query.constraints) {
      visit(cons);
      constraints.set(cntr, itemStack.back());
      itemStack.pop_back();
      assert(workQueueEmpty() && "Work queue not empty");
      ++cntr;
    }
    visit(query.expr);
    q.setQuery(itemStack.back());
    itemStack.pop_back();
    assert(workQueueEmpty() && "Work queue not empty");

    q.setRequestedArrayIndex(unrequestedArrayIndex);
  }

  void visitExpr(const ref<Expr> &expr) {
    auto ec = message->getRoot<T>();
    visit(expr);
    assert(!itemStack.empty());
    ec.setExprIdx(itemStack.back());
    itemStack.pop_back();
  }

  bool workQueueEmpty() { return itemStack.size() == 0; }

  /// Returns size occupied by message in byte
  size_t getUsedSize() {
    return capnp::computeSerializedSizeInWords(*message) * sizeof(capnp::word);
  }

  void visit(const ref<Expr> &e) {
    if (auto ec = dyn_cast<ConstantExpr>(e)) {
      visitConstant(ec);
      return;
    }
    Expr &ep = *e.get();

    // Check if we visited this node already,
    // skip in this case
    auto it = usedExpressions.find(&ep);
    if (it != usedExpressions.end()) {
      itemStack.push_back(std::get<0>(it->second));
      return;
    }

    unsigned count = ep.getNumKids();
    for (unsigned i = 0; i < count; i++)
      visit(ep.getKid(i));

    switch (ep.getKind()) {
    case Expr::NotOptimized:
      visitNotOptimized(static_cast<NotOptimizedExpr &>(ep));
      break;
    case Expr::Read:
      visitRead(static_cast<ReadExpr &>(ep));
      break;
    case Expr::Select:
      visitSelect(static_cast<SelectExpr &>(ep));
      break;
    case Expr::Concat:
      visitConcat(static_cast<ConcatExpr &>(ep));
      break;
    case Expr::Extract:
      visitExtract(static_cast<ExtractExpr &>(ep));
      break;
    case Expr::ZExt:
      visitZExt(static_cast<ZExtExpr &>(ep));
      break;
    case Expr::SExt:
      visitSExt(static_cast<SExtExpr &>(ep));
      break;
    case Expr::Add:
      visitAdd(static_cast<AddExpr &>(ep));
      break;
    case Expr::Sub:
      visitSub(static_cast<SubExpr &>(ep));
      break;
    case Expr::Mul:
      visitMul(static_cast<MulExpr &>(ep));
      break;
    case Expr::UDiv:
      visitUDiv(static_cast<UDivExpr &>(ep));
      break;
    case Expr::SDiv:
      visitSDiv(static_cast<SDivExpr &>(ep));
      break;
    case Expr::URem:
      visitURem(static_cast<URemExpr &>(ep));
      break;
    case Expr::SRem:
      visitSRem(static_cast<SRemExpr &>(ep));
      break;
    case Expr::Not:
      visitNot(static_cast<NotExpr &>(ep));
      break;
    case Expr::And:
      visitAnd(static_cast<AndExpr &>(ep));
      break;
    case Expr::Or:
      visitOr(static_cast<OrExpr &>(ep));
      break;
    case Expr::Xor:
      visitXor(static_cast<XorExpr &>(ep));
      break;
    case Expr::Shl:
      visitShl(static_cast<ShlExpr &>(ep));
      break;
    case Expr::LShr:
      visitLShr(static_cast<LShrExpr &>(ep));
      break;
    case Expr::AShr:
      visitAShr(static_cast<AShrExpr &>(ep));
      break;
    case Expr::Eq:
      visitEq(static_cast<EqExpr &>(ep));
      break;
    case Expr::Ne:
      visitNe(static_cast<NeExpr &>(ep));
      break;
    case Expr::Ult:
      visitUlt(static_cast<UltExpr &>(ep));
      break;
    case Expr::Ule:
      visitUle(static_cast<UleExpr &>(ep));
      break;
    case Expr::Ugt:
      visitUgt(static_cast<UgtExpr &>(ep));
      break;
    case Expr::Uge:
      visitUge(static_cast<UgeExpr &>(ep));
      break;
    case Expr::Slt:
      visitSlt(static_cast<SltExpr &>(ep));
      break;
    case Expr::Sle:
      visitSle(static_cast<SleExpr &>(ep));
      break;
    case Expr::Sgt:
      visitSgt(static_cast<SgtExpr &>(ep));
      break;
    case Expr::Sge:
      visitSge(static_cast<SgeExpr &>(ep));
      break;
    case Expr::Constant:
    default:
      assert(0 && "invalid expression kind");
    }
  }
};

kj::Array<capnp::word> serializeExpression(const ref<Expr> &e) {
  ExpressionSerializer<serial::ExpressionContainer> of;
  of.visitExpr(e);
  of.buildArray();
  of.buildExpressions();

  return of.serialize();
}

void Serializer::serializeExpression(const ref<Expr> &e, bool success) {
  memObj.clearMemory();
  ExpressionSerializer<serial::ExpressionContainer> of(memObj);
  of.visitExpr(e);
  of.buildArray();
  // We don't need to serialize (copy) the expression to a
  // a flat buffer as it is already layed out in the memory referenced by memObj
  assert(of.workQueueEmpty() && "Work queue not empty");
  of.buildExpressions();
  of.setSuccess(success);

  // Remember the space we used inside the memObj
  memObj.setUsedSize(of.getUsedSize());
}

kj::Array<capnp::word>
serializeQuery(const Query &query, const std::vector<const Array *> &arrays) {
  ExpressionSerializer<serial::QueryContainer> of;
  // Populate requested arrays to catch all of them and to keep them in the
  // correct order
  of.populateArray(arrays);
  of.visitQuery(query);
  of.buildArray();
  of.buildExpressions();

  return of.serialize();
}

void Serializer::serializeQuery(const Query &query,
                                const std::vector<const Array *> &arrays) {
  TimerStatIncrementer t(stats::serializerTime);
  memObj.clearMemory();
  ExpressionSerializer<serial::QueryContainer> of(memObj);

  // Populate requested arrays to catch all of them and to keep them in the
  // correct order
  of.populateArray(arrays);
  of.visitQuery(query);
  of.buildArray();
  of.buildExpressions();
  // We don't need to serialize (copy) the query to a
  // a flat buffer as it is already layout in the memory referenced by memObj
  assert(of.workQueueEmpty() && "Work queue not empty");

  // Remember the space we used inside the memObj
  memObj.setUsedSize(of.getUsedSize());
}

///////////////////////////////////////////////////////////////////////////////

void Serializer::serializeComputeInitialValuesAnswer(
    std::vector<std::vector<unsigned char> > &values, bool success,
    bool hasSolution, SolverImpl::SolverRunStatus runStatusCode) {
  memObj.clearMemory();
  capnp::MMapMessageBuilder builder(memObj.getAddr(), memObj.getSize());
  auto root = builder.initRoot<serial::QueryResponse>();
  auto concValues = root.initConcreteValues(values.size());
  for (size_t i = 0, iE = values.size(); i != iE; ++i) {
    concValues.set(i, capnp::Data::Builder(values[i].data(), values[i].size()));
  }
  root.setSolverRunStatus(runStatusCode);
  root.setSuccess(success);
  root.setHasSolution(hasSolution);

  // Remember the space we used inside the memObj
  memObj.setUsedSize(capnp::computeSerializedSizeInWords(builder) *
                     sizeof(capnp::word));
}
///
void Serializer::serializeConstraintLogAnswer(char *str) {
  memObj.clearMemory();
  capnp::MMapMessageBuilder builder(memObj.getAddr(), memObj.getSize());
  auto root = builder.initRoot<serial::ConstraintLogResponse>();
  root.setResponse(str);

  // Remember the space we used inside the memObj
  memObj.setUsedSize(capnp::computeSerializedSizeInWords(builder) *
                     sizeof(capnp::word));
}

void Serializer::serializeComputeTruthAnswer(bool isValid, bool success) {
  memObj.clearMemory();
  capnp::MMapMessageBuilder builder(memObj.getAddr(), memObj.getSize());
  auto root = builder.initRoot<serial::ComputeTruthResponse>();
  root.setIsValid(isValid);
  root.setSuccess(success);

  // Remember the space we used inside the memObj
  memObj.setUsedSize(capnp::computeSerializedSizeInWords(builder) *
                     sizeof(capnp::word));
}

void Serializer::serializeComputeValidityAnswer(Solver::Validity result, bool success) {
  memObj.clearMemory();
  capnp::MMapMessageBuilder builder(memObj.getAddr(), memObj.getSize());
  auto root = builder.initRoot<serial::ComputeValidityResponse>();
  root.setResult(result);
  root.setSuccess(success);

  // Remember the space we used inside the memObj
  memObj.setUsedSize(capnp::computeSerializedSizeInWords(builder) *
                     sizeof(capnp::word));
}


void Serializer::serializeComputeValueAnswer(const ref<Expr> &expr,
                                             bool success) {
  // we workaround and use serializeExpression for this response
  serializeExpression(expr, success);
}

///

template <class T> class ExpressionDeserializer {
  std::map<uint32_t, ref<Expr> > expressions;

  ref<Expr> genExpr(uint32_t idx) {
    auto it = expressions.find(idx);
    if (it != expressions.end())
      return it->second;

    ref<Expr> res;
    auto exp = expressionReader[idx].getPtr();
    switch (exp.which()) {
    default:
      assert(0 && "Type not implemented");
      break;
    case serial::Expr::CONSTANT_EXPR: {
      auto e = exp.getConstantExpr();
      res = ConstantExpr::alloc(e.getValue(), e.getWidth());
      break;
    }
    case serial::Expr::LARGE_CONSTANT_EXPR: {
      auto e = exp.getLargeConstantExpr();
      auto values = e.getValue();
      std::vector<uint64_t> value;
      for (auto val : values)
        value.push_back(val);
      llvm::APInt largeConstant(e.getWidth(), value);
      res = ConstantExpr::alloc(largeConstant);
      break;
    }
    case serial::Expr::READ_EXPR: {
      auto e = exp.getReadExpr();

      // Read Updates
      auto un = getUpdateNode(e.getUpdatesIndex());
      auto ul = UpdateList(arrays[e.getArrayIndex()], un);
      ul.hash();

      res = ReadExpr::alloc(ul, genExpr(e.getIndexExpr()));
      expressions.insert(std::make_pair(idx, res));

      return res;
      break;
    }
    case serial::Expr::EXTRACT_EXPR: {
      auto e = exp.getExtractExpr();
      auto kid = genExpr(e.getKid());
      res = ExtractExpr::alloc(kid, e.getOffset(), e.getWidth());
      break;
    }
#define binaryExpr(name, upper)                                                \
  case serial::Expr::upper##_EXPR: {                                           \
    auto e = exp.get##name##Expr();                                            \
    auto kids = e.getKids();                                                   \
    auto lhs = genExpr(kids[0]);                                               \
    auto rhs = genExpr(kids[1]);                                               \
    res = name##Expr::alloc(lhs, rhs);                                         \
    break;                                                                     \
  }
#define ternaryExpr(name, upper)                                               \
  case serial::Expr::upper##_EXPR: {                                           \
    auto e = exp.get##name##Expr();                                            \
    auto kids = e.getKids();                                                   \
    auto cond = genExpr(kids[0]);                                              \
    auto lhs = genExpr(kids[1]);                                               \
    auto rhs = genExpr(kids[2]);                                               \
    res = name##Expr::alloc(cond, lhs, rhs);                                   \
    break;                                                                     \
  }

#define unaryExpr(name, upper)                                                 \
  case serial::Expr::upper##_EXPR: {                                           \
    auto e = exp.get##name##Expr();                                            \
    auto kids = e.getKids();                                                   \
    auto lhs = genExpr(kids[0]);                                               \
    res = name##Expr::alloc(lhs);                                              \
    break;                                                                     \
  }

#define unarySizeExpr(name, upper)                                             \
  case serial::Expr::upper##_EXPR: {                                           \
    auto e = exp.get##name##Expr();                                            \
    auto kid = genExpr(e.getKid());                                            \
    res = name##Expr::alloc(kid, e.getWidth());                                \
    break;                                                                     \
  }
      unaryExpr(NotOptimized, NOT_OPTIMIZED);

      ternaryExpr(Select, SELECT);
      binaryExpr(Concat, CONCAT);

      unarySizeExpr(ZExt, Z_EXT);
      unarySizeExpr(SExt, S_EXT);

      binaryExpr(Add, ADD);
      binaryExpr(Sub, SUB);
      binaryExpr(Mul, MUL);
      binaryExpr(UDiv, U_DIV);
      binaryExpr(SDiv, S_DIV);
      binaryExpr(URem, U_REM);
      binaryExpr(SRem, S_REM);

      unaryExpr(Not, NOT);
      binaryExpr(And, AND);
      binaryExpr(Or, OR);
      binaryExpr(Xor, XOR);

      binaryExpr(Shl, SHL);
      binaryExpr(LShr, L_SHR) binaryExpr(AShr, A_SHR)

          // Compare
          binaryExpr(Eq, EQ) binaryExpr(Ult, ULT) binaryExpr(Ule, ULE)
              binaryExpr(Slt, SLT) binaryExpr(Sle, SLE)
    }
#undef binaryExpr
#undef unaryExpr
#undef unarySizeExpr

    expressions.insert(std::make_pair(idx, res));
    return res;
  }

  std::unique_ptr<capnp::MessageReader> messageReader;
  const ::capnp::List< ::klee::serial::ExprBox>::Reader expressionReader;
  const ::capnp::List< ::klee::serial::Array>::Reader arrayReader;
  const ::capnp::List< ::klee::serial::UpdateNodeBox>::Reader updateNodeReader;

  void initializeArrays() {
    // Handle Arrays
    for (auto array : arrayReader) {
      std::vector<ref<ConstantExpr> > ce;
      for (auto c : array.getConstantValue()) {
        ref<ConstantExpr> g = dyn_cast<ConstantExpr>(genExpr(c));
        ce.push_back(g);
      }
      auto a = arrayCache->getArray(array.getUid());
      if (!a || ce.empty())
	      arrays.push_back(arrayCache->CreateArray(array.getName(), array.getSize(),
						       &ce[0], &ce[0] + ce.size(),
						       array.getDomain(), array.getRange(),array.getUid()));
      else
	      arrays.push_back(a);
    }
  }

  std::vector<const Array *> arrays;
  uint64_t requestedArrayIndex;
  ArrayCache *arrayCache;

  UpdateNode *getUpdateNode(uint32_t index) {
    if (index == 0)
      return nullptr;

    auto it = updates.find(index);
    if (it != updates.end()) {
      return it->second;
    }
    auto constE = ConstantExpr::create(4, 8);
    auto serNode = updateNodeReader[index - 1].getPtr();
    auto node = new UpdateNode(nullptr, constE, constE);
    updates.insert(std::make_pair(index, node));

    node->index = genExpr(serNode.getIndex());
    node->value = genExpr(serNode.getValue());
    node->next = getUpdateNode(serNode.getNext());
    node->setSize(serNode.getSize());
    node->setHash(serNode.getHashValue());

    return node;
  }

  void initializeExpressions() {
    for (size_t i = 0, j = expressionReader.size(); i < j; ++i) {
      genExpr(i);
    }
  }

  std::unordered_map<uint32_t, UpdateNode *> updates;

public:
  ref<Expr> getExpr() {
    auto ec = messageReader->getRoot<T>();
    initializeArrays();
    initializeExpressions();
    return genExpr(ec.getExprIdx());
  }

  Query getQuery(ConstraintManager &m) {
    auto qc = messageReader->getRoot<T>();
    initializeArrays();
    initializeExpressions();

    for (auto c : qc.getConstraints()) {
      m.addConstraint(genExpr(c));
    }
    requestedArrayIndex = qc.getRequestedArrayIndex();
    return Query(m, genExpr(qc.getQuery()));
  }

  std::vector<const Array *> getArrays() {
    std::vector<const Array *> ar(arrays.begin(),
                                  arrays.begin() + requestedArrayIndex);
    return ar;
  }

  explicit ExpressionDeserializer(
      const kj::ArrayPtr<capnp::word> &messageBuffer, ArrayCache *_arrayCache)
      : messageReader(new capnp::FlatArrayMessageReader(messageBuffer)),
        expressionReader(messageReader->getRoot<T>().getExpressions()),
        arrayReader(messageReader->getRoot<T>().getArrays()),
        updateNodeReader(messageReader->getRoot<T>().getUpdates()),
        requestedArrayIndex(0), arrayCache(_arrayCache) {}
  explicit ExpressionDeserializer(
      kj::ArrayPtr<const kj::ArrayPtr<const capnp::word> > segments,
      ArrayCache *_arrayCache)
      : messageReader(
            new capnp::SegmentArrayMessageReader(segments, getReaderOpts())),
        expressionReader(messageReader->getRoot<T>().getExpressions()),
        arrayReader(messageReader->getRoot<T>().getArrays()),
        updateNodeReader(messageReader->getRoot<T>().getUpdates()),
        requestedArrayIndex(0), arrayCache(_arrayCache) {}

  bool getSuccess() {
    auto qc = messageReader->getRoot<T>();
    return qc.getSuccess();
  }
};

ref<Expr> deserializeExpression(kj::Array<capnp::word> &messageBuffer,
                                ArrayCache *arrayCache) {
  ExpressionDeserializer<serial::ExpressionContainer> ed(messageBuffer.asPtr(),
                                                         arrayCache);
  return ed.getExpr();
}

ref<Expr> Deserializer::deserializeExpression(bool &success) {
  kj::ArrayPtr<const capnp::word> segments[1] = {
      kj::arrayPtr<const capnp::word>(
          reinterpret_cast<const capnp::word *>(memObj.getAddr()),
          memObj.getSize())};
  ExpressionDeserializer<serial::ExpressionContainer> ed(segments, arrayCache);
  success = ed.getSuccess();
  return ed.getExpr();
}

Query deserializeQuery(kj::Array<capnp::word> &messageBuffer,
                       ConstraintManager &m, ArrayCache *arrayCache) {
  ExpressionDeserializer<serial::QueryContainer> ed(messageBuffer, arrayCache);
  return ed.getQuery(m);
}

Query Deserializer::deserializeQuery(ConstraintManager &m) {
  kj::ArrayPtr<const capnp::word> segments[1] = {
      kj::arrayPtr<const capnp::word>(
          reinterpret_cast<const capnp::word *>(memObj.getAddr()),
          memObj.getSize())};
  ExpressionDeserializer<serial::QueryContainer> ed(segments, arrayCache);
  return ed.getQuery(m);
}

Query Deserializer::deserializeQuery(ConstraintManager &m,
                                     std::vector<const Array *> &arrays) {
  kj::ArrayPtr<const capnp::word> segments[1] = {
      kj::arrayPtr<const capnp::word>(
          reinterpret_cast<const capnp::word *>(memObj.getAddr()),
          memObj.getSize())};
  ExpressionDeserializer<serial::QueryContainer> ed(segments, arrayCache);
  auto query = ed.getQuery(m);
  arrays = ed.getArrays();
  return query;
}

void Deserializer::deserializeComputeInitialValuesAnswer(
    std::vector<std::vector<unsigned char> > &values, bool &success,
    bool &hasSolution, SolverImpl::SolverRunStatus &runStatusCode) {
  kj::ArrayPtr<const capnp::word> segments[1] = {
      kj::arrayPtr<const capnp::word>(
          reinterpret_cast<const capnp::word *>(memObj.getAddr()),
          memObj.getSize())};
  capnp::SegmentArrayMessageReader reader(segments, getReaderOpts());
  auto root = reader.getRoot<serial::QueryResponse>();

  auto concValues = root.getConcreteValues();
  for (auto value : concValues) {
    std::vector<unsigned char> v(value.begin(), value.end());
    values.emplace_back(v);
  }

  runStatusCode =
      static_cast<SolverImpl::SolverRunStatus>(root.getSolverRunStatus());
  success = root.getSuccess();
  hasSolution = root.getHasSolution();
}

char *Deserializer::deserializeConstraintLogAnswer() {
  kj::ArrayPtr<const capnp::word> segments[1] = {
      kj::arrayPtr<const capnp::word>(
          reinterpret_cast<const capnp::word *>(memObj.getAddr()),
          memObj.getSize())};
  capnp::SegmentArrayMessageReader reader(segments, getReaderOpts());
  auto root = reader.getRoot<serial::ConstraintLogResponse>();
  return strdup(root.getResponse().cStr());
}
void Deserializer::deserializeComputeTruthAnswer(bool &isValid, bool &success) {
  kj::ArrayPtr<const capnp::word> segments[1] = {
      kj::arrayPtr<const capnp::word>(
          reinterpret_cast<const capnp::word *>(memObj.getAddr()),
          memObj.getSize())};
  capnp::SegmentArrayMessageReader reader(segments, getReaderOpts());
  auto root = reader.getRoot<serial::ComputeTruthResponse>();
  isValid = root.getIsValid();
  success = root.getSuccess();
}


void Deserializer::deserializeComputeValidityAnswer(Solver::Validity &result, bool &success) {
  kj::ArrayPtr<const capnp::word> segments[1] = {
      kj::arrayPtr<const capnp::word>(
          reinterpret_cast<const capnp::word *>(memObj.getAddr()),
          memObj.getSize())};
  capnp::SegmentArrayMessageReader reader(segments, getReaderOpts());
  auto root = reader.getRoot<serial::ComputeValidityResponse>();
  switch (root.getResult()){
  case 1:
    result = Solver::True;
    break;
  case 0:
    result = Solver::Unknown;
    break;
  case -1:
    result = Solver::False;
    break;
  default:
    assert(0 && "New case detected");
  }
  success = root.getSuccess();
}

void Deserializer::deserializeComputeValueAnswer(ref<Expr> &expr,
                                                 bool &success) {
  expr = deserializeExpression(success);
}

} // namespace klee
