//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "BplPrintUtils.h"

std::string smack::translateName(const std::string name) {
  return "$" + name;
}

std::string smack::translateName(const Value* val) {
  assert(val->hasName() && "Value has to have a name");
  const std::string name = EscapeString(val->getName().str());
  if (isa<GlobalVariable>(val)) {
    return "$$" + name;
  } else {
    return "$" + name;
  }
}
