//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef REMOVEUNDEFPTRS_H
#define REMOVEUNDEFPTRS_H

#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"

namespace smack {
using namespace llvm;

class RemoveUndefPtrs : public FunctionPass {

  enum Flags { NO_TIMING_INFO = -1 };
  static const std::string INT_TIMING_COST_METADATA;
  static const std::string INSTRUCTION_NAME_METADATA;

public:
  static char ID; // Class identification, replacement for typeinfo
  RemoveUndefPtrs() : FunctionPass(ID) {}

private:
  bool runOnFunction(Function &F) override;
};

} // namespace smack

#endif // REMOVEUNDEFPTRS_H
