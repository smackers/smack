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
  bool voidFlag;
  std::vector<std::string> arguments;
  VarExpr* returnVar;
  std::vector<Block*> blocks;
  Block* entryBlock;
  std::vector<Value*> vars;
  std::vector<Value*> boolVars;

public:
	Procedure(std::string name) : name(name), voidFlag(true), returnVar(NULL), entryBlock(NULL) {}
	virtual ~Procedure();
	std::string getName() const;
  void setNotVoid();
  bool isVoid() const;
  void addArgument(std::string argument);
  void setReturnVar(VarExpr* var);
  VarExpr* getReturnVar() const;
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
