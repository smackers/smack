//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef ADDTIMING_H
#define ADDTIMING_H

#include "llvm/Pass.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include <string>
#include "smack/Naming.h"


namespace smack {
  using namespace llvm;
  
  class AddTiming : public FunctionPass {

    enum Flags { NO_TIMING_INFO = -1};
    Naming naming;
  public:
    static char ID; // Class identification, replacement for typeinfo
    AddTiming() : FunctionPass(ID), F(nullptr), TTI(nullptr) {}

    /// Returns the expected cost of the instruction.
    /// Returns -1 if the cost is unknown.
    /// Note, this method does not cache the cost calculation and it
    /// can be expensive in some cases.
    unsigned getInstructionCost(const Instruction *I) const;

  private:
    void addTimingMetadata(Instruction *Inst, const std::string &name, const std::string& value) const;
    void addTimingMetadata(Instruction *Inst, const std::string &name, unsigned cost) const;
    void addTimingMetadata(Instruction *Inst, unsigned cost) const;
    void getAnalysisUsage(AnalysisUsage &AU) const override;
    bool runOnFunction(Function &F) override;
    void print(raw_ostream &OS, const Module*) const override;
    std::string nameInstruction(Instruction *Inst) const;
    
    /// The function that we analyze.
    Function *F;
    /// Target information.
    const TargetTransformInfo *TTI;
  };
  
}//namespace smack

#endif //ADDTIMING_H

