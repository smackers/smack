//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Expr.h"

using namespace smack;
using namespace std;

namespace smack {

ostream &operator<<(ostream &os, const Expr* expr) {
  if (expr == 0) {
    os << "<null> Expr!" << endl;
  } else {
    expr->print(os);
  }
  return os;
}
 
ostream &operator<<(ostream &os, const Expr& expr) {
  expr.print(os);
  return os;
}

}
