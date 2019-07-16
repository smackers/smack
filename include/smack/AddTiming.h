//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef ADDTIMING_H
#define ADDTIMING_H

#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"

namespace llvm {
class TargetTransformInfo;
}

namespace smack {
using namespace llvm;

class AddTiming : public FunctionPass {

  enum Flags { NO_TIMING_INFO = -1 };
  static const std::string INT_TIMING_COST_METADATA;
  static const std::string INSTRUCTION_NAME_METADATA;

public:
  static char ID; // Class identification, replacement for typeinfo
  AddTiming() : FunctionPass(ID), F(nullptr), TTI(nullptr) {}

  /// Returns the expected cost of the instruction.
  /// Returns -1 if the cost is unknown.
  /// Note, this method does not cache the cost calculation and it
  /// can be expensive in some cases.
  unsigned getInstructionCost(const Instruction *I) const;

private:
  void addMetadata(Instruction *Inst, const std::string &name,
                   const std::string &value) const;
  void addMetadata(Instruction *Inst, const std::string &name,
                   unsigned cost) const;
  void addNamingMetadata(Instruction *Inst) const;
  void addTimingMetadata(Instruction *Inst) const;

  void getAnalysisUsage(AnalysisUsage &AU) const override;
  bool runOnFunction(Function &F) override;
  void print(raw_ostream &OS, const Module *) const override;
  std::string nameInstruction(Instruction *Inst) const;

  /// The function that we analyze.
  Function *F;
  /// Target information.
  const TargetTransformInfo *TTI;
};

} // namespace smack

#endif // ADDTIMING_H
