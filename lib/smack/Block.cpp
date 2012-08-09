//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Block.h"

using namespace smack;

Block::Block(BasicBlock* block) : basicBlock(block), parentProcedure(NULL) {}

Block::~Block() {}

void Block::addSuccBlock(Block* succBlock) {
  succBlocks.push_back(succBlock);
}

BasicBlock* Block::getBasicBlock() const {
  return basicBlock;
}

std::string Block::getName() const {
  assert(basicBlock->hasName() && "Basic block always has a name");
  return basicBlock->getName();
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

void Block::print(std::ostream &os) const {
  if (this == 0) {
    os << "<null Block>";
  } else {
    os << "label_" << getName() << ":\n";

    printElements(instructions, os);

    if (!succBlocks.empty()) {
      if (const BranchInst* branchInst = dyn_cast<BranchInst>(basicBlock->getTerminator())) {
        if (branchInst->isConditional()) {
          assert(branchInst->getNumSuccessors() == 2 && "Conditional branch has two successors");
          
          Value* conditionValue = branchInst->getCondition();
          assert(conditionValue->hasName() && "Condition has to have a name");
          BasicBlock* trueBlock = branchInst->getSuccessor(0);
          BasicBlock* falseBlock = branchInst->getSuccessor(1);
          
          os << "  goto ";
          os << "$label_" << getName() << "_" << trueBlock->getName().str() << ", ";
          os << "$label_" << getName() << "_" << falseBlock->getName().str();
          os << ";\n";

          os << "$label_" << getName() << "_" << trueBlock->getName().str() << ":\n";
          Expr* trueCondition = new VarExpr(conditionValue);
          os << "  assume " << trueCondition << ";\n";
          os << "  goto label_" << trueBlock->getName().str() << ";\n";

          os << "$label_" << getName() << "_" << falseBlock->getName().str() << ":\n";
          Expr* falseCondition = new NotExpr(new VarExpr(conditionValue));
          os << "  assume " << falseCondition << ";\n";
          os << "  goto label_" << falseBlock->getName().str() << ";\n";
        } else {
          assert(branchInst->getNumSuccessors() == 1 && "Unconditional branch has one successor");
          
          os << "  goto ";
          for(std::vector<Block*>::const_iterator i = succBlocks.begin(), b = succBlocks.begin(),
              e = succBlocks.end(); i != e; ++i) {
            if (i != b) {
              os << ", ";
            }
            os << "label_" << (*i)->getName();
          }
          os << ";\n";
        }
      } else {
        assert(false && "Terminator instruction not currently supported");
      }
    }
  }
}


namespace smack {

std::ostream &operator<<(std::ostream &os, const Block* block) {
  if (block == 0) {
    os << "<null> Block!\n";
  } else {
    block->print(os);
  }
  return os;
}
 
std::ostream &operator<<(std::ostream &os, const Block& block) {
  block.print(os);
  return os;
}

}
