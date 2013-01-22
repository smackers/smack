//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Procedure.h"

using namespace smack;
using namespace std;

Procedure::~Procedure() {}

string Procedure::getName() const {
  return name;
}

void Procedure::setNotVoid() {
  voidFlag = false;
}

bool Procedure::isVoid() const {
  return voidFlag;
}

void Procedure::addArgument(string argument) {
  arguments.push_back(argument);
}

void Procedure::setReturnVar(VarExpr* var) {
  returnVar = var;
}

VarExpr* Procedure::getReturnVar() const {
  return returnVar;
}

void Procedure::setEntryBlock(Block* block) {
  entryBlock = block;
}

Block* Procedure::getEntryBlock() const {
  return entryBlock;
}

void Procedure::addBlock(Block* block) {
  blocks.push_back(block);
  block->setParentProcedure(this);
}

vector<Block*>& Procedure::getBlocks() {
  return blocks;
}

void Procedure::addVariable(Value* var) {
  assert(var->getType()->getTypeID() != Type::VoidTyID && "Variable type shouldn't be void");
  if (!var->hasName()) {
    var->setName("$p");
  }
  vars.push_back(var);
}

void Procedure::addBoolVariable(Value* var) {
  assert(var->getType()->getTypeID() != Type::VoidTyID && "Variable type shouldn't be void");
  if (!var->hasName()) {
    var->setName("$b");
  }
  boolVars.push_back(var);
}

void Procedure::print(ostream &os) const {
  if (this == 0) {
    os << "<null Procedure>";
  } else {
    os << "procedure ";
    if (name != Common::MAIN_PROCEDURE) {
      os << "{:inline 1} ";
    }
    os << name << "(";
    for(vector<string>::const_iterator
        i = arguments.begin(), b = arguments.begin(), e = arguments.end(); i != e; ++i) {
      if (i != b) {
        os << ", ";
      }
      os << *i << ": $ptr";
    }
    os << ")";
    
    if (voidFlag) {
      os << endl;
    } else {
      assert(returnVar != 0 && "Function is not void and return var has to be set");
      os << " returns (" << *returnVar << ": $ptr)" << endl;
    }
    
    os << "modifies $Mem;" << endl;
    os << "modifies $Alloc;" << endl;
    
    os << "{" << endl;
    vector<string> varNames;
    varNames.resize(vars.size());
    transform(vars.begin(), vars.end(), varNames.begin(), getValueName());
    printVarDecls(varNames, os, "$ptr");
    varNames.clear();
    varNames.resize(boolVars.size());
    transform(boolVars.begin(), boolVars.end(), varNames.begin(), getValueName());
    printVarDecls(varNames, os, "bool");

    os << endl;
    
    printElements(blocks, os);
    os << "}" << endl;
  }
}


namespace smack {

ostream &operator<<(ostream &os, const Procedure* proc) {
  if (proc == 0) {
    os << "<null> Procedure!" << endl;
  } else {
    proc->print(os);
  }
  return os;
}
 
ostream &operator<<(ostream &os, const Procedure& proc) {
  proc.print(os);
  return os;
}

}
