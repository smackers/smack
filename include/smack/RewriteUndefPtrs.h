//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef REWRITEUNDEFPTRS_H
#define REWRITEUNDEFPTRS_H

#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"

namespace smack {
using namespace llvm;

class RewriteUndefPtrs : public FunctionPass {

  enum Flags { NO_TIMING_INFO = -1 };
  static const std::string INT_TIMING_COST_METADATA;
  static const std::string INSTRUCTION_NAME_METADATA;

public:
  static char ID; // Class identification, replacement for typeinfo
  RewriteUndefPtrs() : FunctionPass(ID) {}

private:
  bool runOnFunction(Function &F) override;
};

} // namespace smack

#endif // REWRITEUNDEFPTRS_H
