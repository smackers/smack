//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "BPLExpr.h"

using namespace smack;

namespace smack {

std::ostream &operator<<(std::ostream &os, const BPLExpr* expr) {
  if (expr == 0) {
    os << "<null> BPLExpr!\n";
  } else {
    expr->print(os);
  }
  return os;
}
 
std::ostream &operator<<(std::ostream &os, const BPLExpr& expr) {
  expr.print(os);
  return os;
}

}
