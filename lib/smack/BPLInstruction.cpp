//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "BPLInstruction.h"

using namespace smack;

namespace smack {

std::ostream &operator<<(std::ostream &os, const BPLInstruction* inst) {
  if (inst == 0) {
    os << "<null> BPLInst!\n";
  } else {
    inst->print(os);
  }
  return os;
}
 
std::ostream &operator<<(std::ostream &os, const BPLInstruction& inst) {
  inst.print(os);
  return os;
}

}

Instruction* BPLInstruction::getInstruction() const {
  return inst;
}

void BPLInstruction::setParentBlock(BPLBlock* parentBlockP) {
  parentBlock = parentBlockP;
}

BPLBlock* BPLInstruction::getParentBlock() const {
  return parentBlock;
}

void BPLInstruction::print(std::ostream &os) const {
  os << "  ";
}
