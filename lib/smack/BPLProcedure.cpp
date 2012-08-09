//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "BPLProcedure.h"

using namespace smack;

BPLProcedure::~BPLProcedure() {}

std::string BPLProcedure::getName() const {
  return name;
}

void BPLProcedure::setNotVoid() {
  voidFlag = false;
}

bool BPLProcedure::isVoid() const {
  return voidFlag;
}

void BPLProcedure::addArgument(std::string argument) {
  arguments.push_back(argument);
}

void BPLProcedure::setReturnVar(BPLVarExpr* var) {
  returnVar = var;
}

BPLVarExpr* BPLProcedure::getReturnVar() const {
  return returnVar;
}

void BPLProcedure::setEntryBlock(BPLBlock* block) {
  entryBlock = block;
}

BPLBlock* BPLProcedure::getEntryBlock() const {
  return entryBlock;
}

void BPLProcedure::addBlock(BPLBlock* block) {
  blocks.push_back(block);
  block->setParentProcedure(this);
}

std::vector<BPLBlock*>& BPLProcedure::getBlocks() {
  return blocks;
}

void BPLProcedure::addVariable(Value* var) {
  assert(var->getType()->getTypeID() != Type::VoidTyID && "Variable type shoudln't be void");
  if (!var->hasName()) {
    var->setName("smackVar");
  }
  vars.push_back(var);
}

void BPLProcedure::addBoolVariable(Value* var) {
  assert(var->getType()->getTypeID() != Type::VoidTyID && "Variable type shoudln't be void");
  if (!var->hasName()) {
    var->setName("smackVar");
  }
  boolVars.push_back(var);
}

void BPLProcedure::print(std::ostream &os) const {
  if (this == 0) {
    os << "<null BPLProcedure>";
  } else {
    os << "procedure ";
    if (name != Common::MAIN_PROCEDURE) {
      os << "{:inline 1} ";
    }
    os << name << "(";
    for(std::vector<std::string>::const_iterator
        i = arguments.begin(), b = arguments.begin(), e = arguments.end(); i != e; ++i) {
      if (i != b) {
        os << ", ";
      }
      os << *i << ":ptr";
    }
    os << ")";
    
    if (voidFlag) {
      os << "\n";
    } else {
      assert(returnVar != 0 && "Function is not void and return var has to be set");
      os << " returns (" << *returnVar << ":ptr)\n";
    }
    
    os << "modifies Mem;\n";
    os << "modifies Alloc;\n";
    
    os << "{\n";
    std::vector<std::string> varNames;
    varNames.resize(vars.size());
    std::transform(vars.begin(), vars.end(), varNames.begin(), getValueName());
    printVarDecls(varNames, os, "ptr");
    varNames.clear();
    varNames.resize(boolVars.size());
    std::transform(boolVars.begin(), boolVars.end(), varNames.begin(), getValueName());
    printVarDecls(varNames, os, "bool");

    os << "\n";
    
    printElements(blocks, os);
    os << "}\n";
  }
}


namespace smack {

std::ostream &operator<<(std::ostream &os, const BPLProcedure* proc) {
  if (proc == 0) {
    os << "<null> BPLProcedure!\n";
  } else {
    proc->print(os);
  }
  return os;
}
 
std::ostream &operator<<(std::ostream &os, const BPLProcedure& proc) {
  proc.print(os);
  return os;
}

}
