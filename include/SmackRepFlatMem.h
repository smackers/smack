//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKREPFLATMEM_H
#define SMACKREPFLATMEM_H

#include "SmackRep.h"
#include "SmackOptions.h"

namespace smack {

using llvm::Regex;
using llvm::SmallVector;
using llvm::StringRef;
using namespace std;

class SmackRepFlatMem : public SmackRep {

  int globalsTop;

public:
  static const string CURRADDR;
  static const string PTR_TYPE;
  static const string PRELUDE;
  
  static const string MALLOC_PROC;
  static const string ALLOCA_PROC;
  static const string FREE_PROC;
  
  static const string MALLOC_IMPL;
  static const string ALLOCA_IMPL;
  static const string FREE_IMPL;

public:
  SmackRepFlatMem(llvm::DataLayout* td) : SmackRep(td), globalsTop(0) {}
  virtual vector<const Decl*> globalDecl(const llvm::Value* g);
  virtual vector<string> getModifies();
  virtual string getPtrType();
  virtual string getPrelude();
};
}

#endif // SMACKREPFLATMEM_H

