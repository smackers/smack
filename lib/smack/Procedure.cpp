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

bool Procedure::isVoid() const {
  return returnType->isVoidTy();
}

bool Procedure::isBoolean() const {
  return returnType->isIntegerTy(1);
}

void Procedure::addArgument(const llvm::Argument *arg) {
  arguments.push_back(arg);
}

vector<const llvm::Argument*>& Procedure::getArguments() {
  return arguments;
}

void Procedure::setReturnVar(VarExpr* var) {
  returnVar = var;
}

VarExpr* Procedure::getReturnVar() const {
  return returnVar;
}

bool Procedure::isDefined() const {
  return !blocks.empty();
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
    os << name << "(";    
    for (int i=0, n=arguments.size(); i<n; i++)
      os << translateName(arguments[i])
         << ": " << (arguments[i]->getType()->isIntegerTy(1) ? "bool" : "$ptr")
         << (i<n-1 ? ", " : "");    
    os << ")";
    
    assert ((isVoid() || returnVar != NULL) 
      && "Function is not void and return var has to be set");

    if (isDefined()) {
      if (!isVoid())
        os << " returns (" << *returnVar << ": " << (isBoolean() ? "bool" : "$ptr") << ")";
      os << endl;    
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
    } else {
      if (!isVoid())
        os << " returns ($r: " << (isBoolean() ? "bool" : "$ptr") << ")";
      os << ";" << endl;      
    }
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
