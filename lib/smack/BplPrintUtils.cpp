//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "BplPrintUtils.h"

using namespace std;

string smack::translateName(const string name) {
  return "" + name;
}

string smack::translateName(const Value* val) {
  assert(val->hasName() && "Value has to have a name");
  const string name = EscapeString(val->getName().str());
  if (isa<GlobalVariable>(val)) {
    return "" + name;
  } else {
    return "" + name;
  }
}
