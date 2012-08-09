//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Statement.h"

using namespace smack;

namespace smack {

std::ostream &operator<<(std::ostream &os, const Statement* inst) {
  if (inst == 0) {
    os << "<null> BPLInst!\n";
  } else {
    inst->print(os);
  }
  return os;
}
 
std::ostream &operator<<(std::ostream &os, const Statement& inst) {
  inst.print(os);
  return os;
}

}

void Statement::setParentBlock(BPLBlock* parentBlockP) {
  parentBlock = parentBlockP;
}

BPLBlock* Statement::getParentBlock() const {
  return parentBlock;
}

void Statement::print(std::ostream &os) const {
  os << "  ";
}
