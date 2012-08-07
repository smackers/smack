//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "BPLBlock.h"

using namespace smack;

BPLBlock::BPLBlock(BasicBlock* block) : basicBlock(block), parentProcedure(NULL) {}

BPLBlock::~BPLBlock() {}

void BPLBlock::addSuccBlock(BPLBlock* succBlock) {
  succBlocks.push_back(succBlock);
}

BasicBlock* BPLBlock::getBasicBlock() const {
  return basicBlock;
}

std::string BPLBlock::getName() const {
  assert(basicBlock->hasName() && "Basic block always has a name");
  return basicBlock->getName();
}

void BPLBlock::addInstruction(BPLInstruction* inst) {
  instructions.push_back(inst);
  inst->setParentBlock(this);
}

void BPLBlock::setParentProcedure(BPLProcedure* parentProc) {
  parentProcedure = parentProc;
}

BPLProcedure* BPLBlock::getParentProcedure() const {
  return parentProcedure;
}

void BPLBlock::print(std::ostream &os) const {
  if (this == 0) {
    os << "<null BPLBlock>";
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
          BPLExpr* trueCondition = new BPLVarExpr(conditionValue);
          os << "  assume " << trueCondition << ";\n";
          os << "  goto label_" << trueBlock->getName().str() << ";\n";

          os << "$label_" << getName() << "_" << falseBlock->getName().str() << ":\n";
          BPLExpr* falseCondition = new BPLNotExpr(new BPLVarExpr(conditionValue));
          os << "  assume " << falseCondition << ";\n";
          os << "  goto label_" << falseBlock->getName().str() << ";\n";
        } else {
          assert(branchInst->getNumSuccessors() == 1 && "Unconditional branch has one successor");
          
          os << "  goto ";
          for(std::vector<BPLBlock*>::const_iterator i = succBlocks.begin(), b = succBlocks.begin(),
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

std::ostream &operator<<(std::ostream &os, const BPLBlock* block) {
  if (block == 0) {
    os << "<null> BPLBlock!\n";
  } else {
    block->print(os);
  }
  return os;
}
 
std::ostream &operator<<(std::ostream &os, const BPLBlock& block) {
  block.print(os);
  return os;
}

}
