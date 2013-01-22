//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef PROCEDURE_H_
#define PROCEDURE_H_

#include "Block.h"
#include "BplPrintUtils.h"
#include "Utils.h"
#include <map>
#include <sstream>

using namespace llvm;

namespace smack {

class AnnoExpr;

class Procedure {
private:
  std::string name;
  llvm::Type *returnType;
  std::vector<const llvm::Argument*> arguments;
  VarExpr* returnVar;
  std::vector<Block*> blocks;
  Block* entryBlock;
  std::vector<Value*> vars;
  std::vector<Value*> boolVars;

public:
	Procedure(std::string name, llvm::Type *returnTypeP)
    : name(name), returnType(returnTypeP), returnVar(NULL), entryBlock(NULL) {}
	virtual ~Procedure();
	std::string getName() const;
  bool isVoid() const;
  bool isBoolean() const;
  void addArgument(const llvm::Argument *arg);
  std::vector<const llvm::Argument*>& getArguments();
  void setReturnVar(VarExpr* var);
  VarExpr* getReturnVar() const;
  bool isDefined() const;
	void setEntryBlock(Block* block);
  Block* getEntryBlock() const;
  void addBlock(Block* block);
  std::vector<Block*>& getBlocks();
  void addVariable(Value* var);
  void addBoolVariable(Value* var);
  void print(std::ostream &os) const;
};
std::ostream &operator<<(std::ostream &os, const Procedure* proc);
std::ostream &operator<<(std::ostream &os, const Procedure& proc);

}

#endif /*PROCEDURE_H_*/
