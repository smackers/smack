//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKREPFLATMEM_H
#define SMACKREPFLATMEM_H

#include "smack/SmackRep.h"

namespace smack {

using llvm::Regex;
using llvm::SmallVector;
using llvm::StringRef;
using namespace std;

class SmackRepFlatMem : public SmackRep {

  int bottom;

public:
  SmackRepFlatMem(DSAAliasAnalysis* aa) : SmackRep(aa), bottom(0) {}
  virtual vector<Decl*> globalDecl(const llvm::Value* g);
  virtual string getPtrType();
  
  const Expr* declareIsExternal(const Expr* e);

  virtual string memoryModel();
  virtual string memcpyProc(int dstReg, int srcReg);
  virtual string memsetProc(int dstReg);
};
}

#endif // SMACKREPFLATMEM_H

