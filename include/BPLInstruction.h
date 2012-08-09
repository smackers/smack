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
  enum InstructionIDs {
    AssignInstID,
    CallInstID,
    CmpInstID,
    BoolToIntInstID,
    TruncInstID,
    BinaryOperatorInstID,
    AllocaInstID,
    MallocInstID,
    FreeInstID,
    AssertInstID,
    AssumeInstID,
    ReturnInstID,
    SelectInstID
  };

private:
  InstructionIDs id;
  
protected:
  Instruction* inst;
  BPLBlock* parentBlock;
  
public:
  BPLInstruction(InstructionIDs idP, Instruction* instP) : id(idP), inst(instP) {}
	virtual ~BPLInstruction() {}
  void setParentBlock(BPLBlock* parentBlockP);
  BPLBlock* getParentBlock() const;
  virtual void print(std::ostream &os) const;
  
  inline InstructionIDs getInstructionID() const {
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
