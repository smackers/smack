//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef PROCEDURE_H_
#define PROCEDURE_H_

#include "BPLBlock.h"
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
  BPLVarExpr* returnVar;
  std::vector<BPLBlock*> blocks;
  BPLBlock* entryBlock;
  std::vector<Value*> vars;
  std::vector<Value*> boolVars;

public:
	Procedure(std::string name) : name(name), voidFlag(true), returnVar(NULL), entryBlock(NULL) {}
	virtual ~Procedure();
	std::string getName() const;
  void setNotVoid();
  bool isVoid() const;
  void addArgument(std::string argument);
  void setReturnVar(BPLVarExpr* var);
  BPLVarExpr* getReturnVar() const;
	void setEntryBlock(BPLBlock* block);
  BPLBlock* getEntryBlock() const;
  void addBlock(BPLBlock* block);
  std::vector<BPLBlock*>& getBlocks();
  void addVariable(Value* var);
  void addBoolVariable(Value* var);
  void print(std::ostream &os) const;
};
std::ostream &operator<<(std::ostream &os, const Procedure* proc);
std::ostream &operator<<(std::ostream &os, const Procedure& proc);

}

#endif /*PROCEDURE_H_*/
