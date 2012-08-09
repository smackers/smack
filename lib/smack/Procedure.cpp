//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Procedure.h"

using namespace smack;

Procedure::~Procedure() {}

std::string Procedure::getName() const {
  return name;
}

void Procedure::setNotVoid() {
  voidFlag = false;
}

bool Procedure::isVoid() const {
  return voidFlag;
}

void Procedure::addArgument(std::string argument) {
  arguments.push_back(argument);
}

void Procedure::setReturnVar(VarExpr* var) {
  returnVar = var;
}

VarExpr* Procedure::getReturnVar() const {
  return returnVar;
}

void Procedure::setEntryBlock(BPLBlock* block) {
  entryBlock = block;
}

BPLBlock* Procedure::getEntryBlock() const {
  return entryBlock;
}

void Procedure::addBlock(BPLBlock* block) {
  blocks.push_back(block);
  block->setParentProcedure(this);
}

std::vector<BPLBlock*>& Procedure::getBlocks() {
  return blocks;
}

void Procedure::addVariable(Value* var) {
  assert(var->getType()->getTypeID() != Type::VoidTyID && "Variable type shoudln't be void");
  if (!var->hasName()) {
    var->setName("smackVar");
  }
  vars.push_back(var);
}

void Procedure::addBoolVariable(Value* var) {
  assert(var->getType()->getTypeID() != Type::VoidTyID && "Variable type shoudln't be void");
  if (!var->hasName()) {
    var->setName("smackVar");
  }
  boolVars.push_back(var);
}

void Procedure::print(std::ostream &os) const {
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

std::ostream &operator<<(std::ostream &os, const Procedure* proc) {
  if (proc == 0) {
    os << "<null> BPLProcedure!\n";
  } else {
    proc->print(os);
  }
  return os;
}
 
std::ostream &operator<<(std::ostream &os, const Procedure& proc) {
  proc.print(os);
  return os;
}

}
