//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/InstVisitor.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include <unordered_set>

using namespace std;

namespace llvm {

  unordered_set<Instruction*> getSlice(Value* V);

  Function* slice(Value* V);

}
