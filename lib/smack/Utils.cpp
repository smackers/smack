//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Utils.h"

using namespace smack;

namespace smack {

std::string EscapeString(std::string str) {
  str = llvm::DOT::EscapeString(str);
  return str;
}

}
