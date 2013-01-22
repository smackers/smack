//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Utils.h"

using namespace smack;
using namespace std;

namespace smack {

string EscapeString(string str) {
  str = llvm::DOT::EscapeString(str);
  return str;
}

}
