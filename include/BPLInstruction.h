//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLINSTRUCTION_H_
#define BPLINSTRUCTION_H_

#include "Exprs.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

namespace smack {

class BPLBlock;

class BPLInstruction {
public:
  enum BPLInstructionIDs {
    BPLAssignInstID,
    BPLCallInstID,
    BPLCmpInstID,
    BPLBoolToIntInstID,
    BPLTruncInstID,
    BPLBinaryOperatorInstID,
    BPLAllocaInstID,
    BPLMallocInstID,
    BPLFreeInstID,
    BPLAssertInstID,
    BPLAssumeInstID,
    BPLReturnInstID,
    BPLSelectInstID
  };

private:
  BPLInstructionIDs id;
  
protected:
  Instruction* inst;
  BPLBlock* parentBlock;
  
public:
  BPLInstruction(BPLInstructionIDs idP, Instruction* instP) : id(idP), inst(instP) {}
	virtual ~BPLInstruction() {}
  void setParentBlock(BPLBlock* parentBlockP);
  BPLBlock* getParentBlock() const;
  virtual void print(std::ostream &os) const;
  
  inline BPLInstructionIDs getBPLInstructionID() const {
    return id;
  }
  
  static inline bool classof(const BPLInstruction* inst) {
    return true;
  }
};
std::ostream &operator<<(std::ostream &os, const BPLInstruction* inst);
std::ostream &operator<<(std::ostream &os, const BPLInstruction& inst);

}

#endif /*BPLINSTRUCTION_H_*/
