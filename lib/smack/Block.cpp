//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Block.h"
#include <string>

using namespace smack;
using namespace std;

Block::Block(BasicBlock* block, int blockNum) : 
  basicBlock(block), parentProcedure(NULL), blockNum(blockNum) {}

Block::~Block() {}

void Block::addSuccBlock(Block* succBlock) {
  succBlocks.push_back(succBlock);
}

BasicBlock* Block::getBasicBlock() const {
  return basicBlock;
}

string Block::getName() const {
  stringstream s;
  if (basicBlock->hasName())
    return basicBlock->getName();
  else {
    s << "$bb" << blockNum;
    return s.str();
  }
}

void Block::addInstruction(Statement* inst) {
  instructions.push_back(inst);
  inst->setParentBlock(this);
}

void Block::setParentProcedure(Procedure* parentProc) {
  parentProcedure = parentProc;
}

Procedure* Block::getParentProcedure() const {
  return parentProcedure;
}

void Block::print(ostream &os) const {
  if (this == 0) {
    os << "<null Block>";
  } else {
    os << getName() << ":" << endl;

    printElements(instructions, os);

    if (!succBlocks.empty()) {
      if (const BranchInst* branchInst = dyn_cast<BranchInst>(basicBlock->getTerminator())) {
        if (branchInst->isConditional()) {
          assert(branchInst->getNumSuccessors() == 2 
            && "Conditional branch has two successors");

          Expr
            *te = new VarExpr(branchInst->getCondition()),
            *fe = new NotExpr(te);      
                  
          BasicBlock 
            *tb = branchInst->getSuccessor(0);
                  
          os << "  goto " << getName() << "$T, " << getName() << "$F;" << endl;          
            
          for ( vector<Block*>::const_iterator 
                  head = succBlocks.begin(), 
                  curr = head, tail = succBlocks.end();
                curr != tail;
                ++curr ) {
                                    
            BasicBlock *bb = (*curr)->basicBlock;                  
            os << getName() << "$" << (bb == tb ? "T" : "F") << ":" << endl;
            os << "  assume " << (bb == tb ? te : fe) << ";" << endl;
            os << "  goto " << (*curr)->getName() << ";" << endl;            
          }
          
        } else {
          assert(branchInst->getNumSuccessors() == 1 
            && "Unconditional branch has one successor");
          
          os << "  goto " << succBlocks[0]->getName() << ";" << endl;
        }
      } else {
        assert(false && "Terminator instruction not currently supported");
      }
    }
  }
}


namespace smack {

ostream &operator<<(ostream &os, const Block* block) {
  if (block == 0) {
    os << "<null> Block!" << endl;
  } else {
    block->print(os);
  }
  return os;
}
 
ostream &operator<<(ostream &os, const Block& block) {
  block.print(os);
  return os;
}

}
