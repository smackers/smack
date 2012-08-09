//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BLOCK_H_
#define BLOCK_H_

#include "Statements.h"
#include "Utils.h"
#include "llvm/BasicBlock.h"
#include <set>
#include <vector>

using namespace llvm;

namespace smack {

class Procedure;

class Block {
private:
  std::vector<Block*> succBlocks;
  BasicBlock* basicBlock;
  std::vector<Statement*> instructions;
  Procedure* parentProcedure;
  
public:
	Block(BasicBlock* block);
	virtual ~Block();
	void addSuccBlock(Block* succBlock);
  BasicBlock* getBasicBlock() const;
  std::string getName() const;
  void addInstruction(Statement* inst);
  void setParentProcedure(Procedure* parentProc);
  Procedure* getParentProcedure() const;
  void print(std::ostream &os) const;
};
std::ostream &operator<<(std::ostream &os, const Block* block);
std::ostream &operator<<(std::ostream &os, const Block& block);

}

#endif /*BLOCK_H_*/
