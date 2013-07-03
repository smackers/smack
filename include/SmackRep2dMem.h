//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKREP2DMEM_H
#define SMACKREP2DMEM_H

#include "SmackRep.h"

namespace smack {

using llvm::Regex;
using llvm::SmallVector;
using llvm::StringRef;
using namespace std;

class SmackRep2dMem : public SmackRep {
public:
  static const string PTR_TYPE;
  static const string REF_TYPE;
  static const string PRELUDE;

public:
  SmackRep2dMem(llvm::DataLayout* td) : SmackRep(td) {}
  virtual vector<const Decl*> globalDecl(const llvm::Value* g);
  virtual vector<string> getModifies();
  virtual string getPtrType();
  virtual string getPrelude();
};
}

#endif // SMACKREP2DMEM_H

