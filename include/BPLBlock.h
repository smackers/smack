//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLBLOCK_H_
#define BPLBLOCK_H_

#include "Statements.h"
#include "Utils.h"
#include "llvm/BasicBlock.h"
#include <set>
#include <vector>

using namespace llvm;

namespace smack {

class Procedure;

class BPLBlock {
private:
  std::vector<BPLBlock*> succBlocks;
  BasicBlock* basicBlock;
  std::vector<Statement*> instructions;
  Procedure* parentProcedure;
  
public:
	BPLBlock(BasicBlock* block);
	virtual ~BPLBlock();
	void addSuccBlock(BPLBlock* succBlock);
  BasicBlock* getBasicBlock() const;
  std::string getName() const;
  void addInstruction(Statement* inst);
  void setParentProcedure(Procedure* parentProc);
  Procedure* getParentProcedure() const;
  void print(std::ostream &os) const;
};
std::ostream &operator<<(std::ostream &os, const BPLBlock* block);
std::ostream &operator<<(std::ostream &os, const BPLBlock& block);

}

#endif /*BPLBLOCK_H_*/
