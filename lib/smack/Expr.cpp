//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Expr.h"

using namespace smack;

namespace smack {

std::ostream &operator<<(std::ostream &os, const Expr* expr) {
  if (expr == 0) {
    os << "<null> BPLExpr!\n";
  } else {
    expr->print(os);
  }
  return os;
}
 
std::ostream &operator<<(std::ostream &os, const Expr& expr) {
  expr.print(os);
  return os;
}

}
