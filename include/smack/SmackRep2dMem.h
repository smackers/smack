//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKREP2DMEM_H
#define SMACKREP2DMEM_H

#include "smack/SmackRep.h"

namespace smack {

using llvm::Regex;
using llvm::SmallVector;
using llvm::StringRef;
using namespace std;

// NOTE: TwoDim memory model has no good (sound or precise) support for
// ptr2int and int2ptr operations.
class SmackRep2dMem : public SmackRep {
public:
  static const string PTR_TYPE;
  static const string REF_TYPE;
  static const string POINTERS;
  static const string STATIC;
  static const string EXTERN;

public:
  SmackRep2dMem(DSAAliasAnalysis* aa) : SmackRep(aa) {}
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

#endif // SMACKREP2DMEM_H

