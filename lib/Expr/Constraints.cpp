//===-- Constraints.cpp ---------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Constraints.h"

#include "klee/util/ExprPPrinter.h"
#include "klee/util/ExprVisitor.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Function.h"
#else
#include "llvm/Function.h"
#endif
#include "llvm/Support/CommandLine.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/TimerStatIncrementer.h"
#include "klee/SolverStats.h"

#include <map>

using namespace klee;

namespace {
llvm::cl::opt<bool> RewriteEqualities(
    "rewrite-equalities", llvm::cl::init(true),
    llvm::cl::desc("Rewrite existing constraints when an equality with a "
                   "constant is added (default=on)"));
}

void ConstraintSetView::extractAndResetConstraints(ConstraintSetView &other) {
  constraints.swap(other.constraints);
  origPosition.swap(other.origPosition);
//  deletedPositions.swap(other.deletedPositions);
//  std::swap(uid_cntr, other.uid_cntr);
//  std::swap(next_free_position, other.next_free_position);
}

void ConstraintSetView::dump() const {
  size_t i = 0;
  for (const_iterator it = constraints.begin(), itE = constraints.end();
       it != itE; ++it) {
    llvm::errs() << "{" << origPosition[i].origin << "/"<< origPosition[i].unique << "}";
    ++i;
    (*it)->dump();
  }
}

class ExprReplaceVisitor : public ExprVisitor {
private:
  ref<Expr> src, dst;

public:
  ExprReplaceVisitor(ref<Expr> _src, ref<Expr> _dst) : src(_src), dst(_dst) {}

  Action visitExpr(const Expr &e) {
    if (e == *src.get()) {
      return Action::changeTo(dst);
    } else {
      return Action::doChildren();
    }
  }

  Action visitExprPost(const Expr &e) {
    if (e == *src.get()) {
      return Action::changeTo(dst);
    } else {
      return Action::doChildren();
    }
  }
};

class ExprReplaceVisitor2 : public ExprVisitor {
private:
  const std::map<ref<Expr>, ref<Expr> > &replacements;

public:
  ExprReplaceVisitor2(const std::map<ref<Expr>, ref<Expr> > &_replacements)
      : ExprVisitor(true), replacements(_replacements) {}

  Action visitExprPost(const Expr &e) {
    std::map<ref<Expr>, ref<Expr> >::const_iterator it =
        replacements.find(ref<Expr>(const_cast<Expr *>(&e)));
    if (it != replacements.end()) {
      return Action::changeTo(it->second);
    } else {
      return Action::doChildren();
    }
  }
};

bool ConstraintManager::rewriteConstraints(ExprVisitor &visitor) {
  ConstraintSetView old;
  bool changed = false;

  constraintSetView.extractAndResetConstraints(old);
  for (ConstraintSetView::iterator it = old.constraints.begin(),
                                   ie = old.constraints.end();
       it != ie; ++it) {
    ref<Expr> &ce = *it;
    ref<Expr> e = visitor.visit(ce);

    auto positions = old.getPositions(it);

    if (e != ce) {
      addConstraintInternal(e, ConstraintPosition(positions.origin, constraintSetView.uid_cntr++)); // enable further reductions
      changed = true;
    } else {
      constraintSetView.push_back(ce, std::move(positions));
    }
  }

  return changed;
}

ref<Expr> ConstraintManager::simplifyExpr(ref<Expr> e,
                                          const ConstraintSetView &view) {
  if (isa<ConstantExpr>(e))
    return e;

  std::map<ref<Expr>, ref<Expr> > equalities;

  for (ConstraintSetView::constraints_ty::const_iterator
           it = view.constraints.begin(),
           ie = view.constraints.end();
       it != ie; ++it) {
    if (const EqExpr *ee = dyn_cast<EqExpr>(*it))
      if (isa<ConstantExpr>(ee->left)) {
        equalities.insert(std::make_pair(ee->right, ee->left));
        continue;
    }
    equalities.insert(std::make_pair(*it, ConstantExpr::alloc(1, Expr::Bool)));
  }

  return ExprReplaceVisitor2(equalities).visit(e);
}

ref<Expr> ConstraintManager::simplifyExpr(ref<Expr> e) {
  return ConstraintManager::simplifyExpr(e, constraintSetView);
}

void ConstraintManager::addConstraintInternal(ref<Expr> e,
                                              ConstraintPosition &&position) {
  // rewrite any known equalities and split Ands into different conjuncts

  switch (e->getKind()) {
  case Expr::Constant:
    assert(cast<ConstantExpr>(e)->isTrue() &&
           "attempt to add invalid (false) constraint");
    constraintSetView.deletedPositions.insert(position);
    break;

  // split to enable finer grained independence and other optimizations
  case Expr::And: {
    BinaryExpr *be = cast<BinaryExpr>(e);
    addConstraintInternal(be->left, ConstraintPosition(position.origin, constraintSetView.uid_cntr++));
    addConstraintInternal(be->right, ConstraintPosition(position.origin, constraintSetView.uid_cntr++));
    break;
  }

  case Expr::Eq: {
    if (RewriteEqualities) {
      // XXX: should profile the effects of this and the overhead.
      // traversing the constraints looking for equalities is hardly the
      // slowest thing we do, but it is probably nicer to have a
      // ConstraintSet ADT which efficiently remembers obvious patterns
      // (byte-constant comparison).
      BinaryExpr *be = cast<BinaryExpr>(e);
      if (isa<ConstantExpr>(be->left)) {
        ExprReplaceVisitor visitor(be->right, be->left);
        rewriteConstraints(visitor);
      }
    }
    constraintSetView.push_back(e, std::move(position));
    break;
  }

  default:
    constraintSetView.push_back(e, std::move(position));
    break;
  }
}

void ConstraintManager::addConstraint(ref<Expr> e) {
  TimerStatIncrementer t(stats::addConstraintTime);

  e = simplifyExpr(e);
  addConstraintInternal(
      e, ConstraintPosition(constraintSetView.next_free_position++, 0));
}
