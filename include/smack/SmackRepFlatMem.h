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
  static const string CURRADDR;
  static const string BOTTOM;
  static const string IS_EXT;
  static const string PTR_TYPE;
  static const string POINTERS;  

public:
  SmackRepFlatMem(DSAAliasAnalysis* aa) : SmackRep(aa), bottom(0) {}
  virtual vector<Decl*> globalDecl(const llvm::Value* g);
  virtual vector<string> getModifies();
  virtual string getPtrType();
  
  const Expr* ptr2ref(const Expr* e);
  const Expr* ptr2val(const Expr* e);
  const Expr* val2ptr(const Expr* e);
  const Expr* ref2ptr(const Expr* e);
  
  const Expr* trunc(const Expr* e, llvm::Type* t);

  const Expr* declareIsExternal(const Expr* e);

  virtual string memoryModel();
  virtual string mallocProc();
  virtual string freeProc();
  virtual string allocaProc();
  virtual string memcpyProc(int dstReg, int srcReg);
};
}

#endif // SMACKREPFLATMEM_H

