//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef STATEMENT_H_
#define STATEMENT_H_

#include "Exprs.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

namespace smack {

class Block;

class Statement {
public:
  enum StatementIDs {
    AssignStmtID,
    CallStmtID,
    CmpStmtID,
    BoolToIntStmtID,
    TruncStmtID,
    BinaryOperatorStmtID,
    AllocaStmtID,
    MallocStmtID,
    FreeStmtID,
    AssertStmtID,
    AssumeStmtID,
    ReturnStmtID,
    SelectStmtID
  };

private:
  StatementIDs id;
  
protected:
  Instruction* inst;
  Block* parentBlock;
  
public:
  Statement(StatementIDs idP, Instruction* instP) : id(idP), inst(instP) {}
	virtual ~Statement() {}
  void setParentBlock(Block* parentBlockP);
  Block* getParentBlock() const;
  virtual void print(std::ostream &os) const;
  
 StatementIDs getStatementID() const {
    return id;
  }
  
  static inline bool classof(const Statement* inst) {
    return true;
  }
};
std::ostream &operator<<(std::ostream &os, const Statement* inst);
std::ostream &operator<<(std::ostream &os, const Statement& inst);

}

#endif /*STATEMENT_H_*/
