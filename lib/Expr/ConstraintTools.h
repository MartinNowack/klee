/*
 * ConstraintTools.h
 *
 *  Created on: 25 Feb 2017
 *      Author: martin
 */

#ifndef LIB_EXPR_CONSTRAINTTOOLS_H_
#define LIB_EXPR_CONSTRAINTTOOLS_H_

#include "klee/util/ExprVisitor.h"

namespace klee {

class ExprCountVisitor : public ExprVisitor {
private:
  uint64_t counter;

protected:
  Action visitExprPost(const Expr &e) {
    ++counter;
    return Action::skipChildren();
  }

  Action visitRead(const ReadExpr &re) {
    const UpdateList &ul = re.updates;

    for (const UpdateNode *un = ul.head; un; un = un->next) {
      visit(un->index);
      visit(un->value);
    }

    return Action::doChildren();
  }

public:
  ExprCountVisitor() : ExprVisitor(false), counter(0) {}

  uint64_t getCounter() { return counter; }
};
}

#endif /* LIB_EXPR_CONSTRAINTTOOLS_H_ */
