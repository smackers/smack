//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLBLOCK_H_
#define BPLBLOCK_H_

#include "BPLInstructions.h"
#include "Utils.h"
#include "llvm/BasicBlock.h"
#include <set>
#include <vector>

using namespace llvm;

namespace smack {

class BPLProcedure;

class BPLBlock {
private:
  std::vector<BPLBlock*> succBlocks;
  BasicBlock* basicBlock;
  std::vector<BPLInstruction*> instructions;
  BPLProcedure* parentProcedure;
  
public:
	BPLBlock(BasicBlock* block);
	virtual ~BPLBlock();
	void addSuccBlock(BPLBlock* succBlock);
  BasicBlock* getBasicBlock() const;
  std::string getName() const;
  void addInstruction(BPLInstruction* inst);
  void setParentProcedure(BPLProcedure* parentProc);
  BPLProcedure* getParentProcedure() const;
  void print(std::ostream &os) const;
};
std::ostream &operator<<(std::ostream &os, const BPLBlock* block);
std::ostream &operator<<(std::ostream &os, const BPLBlock& block);

}

#endif /*BPLBLOCK_H_*/
