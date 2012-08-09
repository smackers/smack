//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLPRINTUTILS_H_
#define BPLPRINTUTILS_H_

#include "Utils.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Value.h"
#include <algorithm>
#include <ostream>
#include <string>

using namespace llvm;

namespace smack {

class printVarDecl {
private:
  std::ostream &os;
  std::string varType;
  
public:
  printVarDecl(std::ostream &stream, std::string varTypeP) : os(stream), varType(varTypeP) {}
  void operator()(std::string var) {
    os << "var " << var << " : " << varType << ";\n";
  }
};

template <class CT> void printVarDecls(const CT& collection, std::ostream& os, std::string varType) {
  std::for_each(collection.begin(), collection.end(), printVarDecl(os, varType));
}

std::string translateName(const std::string name);
std::string translateName(const Value* val);

struct getValueName {
  std::string operator()(Value* val) {
    assert(val->hasName() && "Value has to have a name");
    return translateName(val->getName());
  }
};

}

#endif /*BPLPRINTUTILS_H_*/
