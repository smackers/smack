//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef STATEMENTS_H_
#define STATEMENTS_H_

#include "Statement.h"

namespace smack {

class AssignStmt : public Statement {
private:
  Expr* left;
  Expr* right;

public:
  AssignStmt(Instruction* instP, Expr* leftP, Expr* rightP) :
    Statement(AssignStmtID, instP), left(leftP), right(rightP) {}
  virtual ~AssignStmt() {}
  Expr* getLeft() const;
  Expr* getRight() const;
  virtual void print(std::ostream &os) const;

  static inline bool classof(const AssignStmt* inst) {
    return true;
  }

  static inline bool classof(const Statement* inst) {
    return inst->getStatementID() == AssignStmtID;
  }  
};

class CalledFunction {
private:
  const Function* calledFunction;

public:
  CalledFunction(const Function* calledFunc) : calledFunction(calledFunc) {}
  const Function* getCalledFunction();

  static void destroy(const CalledFunction* calledFunc) {
    delete calledFunc;
  }
};

class CallStmt : public Statement {
private:
  std::vector<CalledFunction*> calledFunctions;
  VarExpr* returnVar;
  VarExpr* functionPointer;
  std::vector<Expr*> params;

public:
  CallStmt(Instruction* instP) : Statement(CallStmtID, instP), returnVar(NULL), functionPointer(NULL) {}
  virtual ~CallStmt();
  CalledFunction* addCalledFunction(const Function* func);
  void setReturnVar(VarExpr* returnVarP);
  void setFunctionPointer(VarExpr* functionPointerP);
  void addParam(Expr* param);
  virtual void print(std::ostream &os) const;

  static inline bool classof(const CallStmt* inst) {
    return true;
  }

  static inline bool classof(const Statement* inst) {
    return inst->getStatementID() == CallStmtID;
  }  
};

class CmpStmt : public Statement {
private:
  Expr* left;
  Expr* right;

public:
  CmpStmt(Instruction* instP, Expr* leftP, Expr* rightP) :
    Statement(CmpStmtID, instP), left(leftP), right(rightP) {}
  virtual ~CmpStmt() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const CmpStmt* inst) {
    return true;
  }

  static inline bool classof(const Statement* inst) {
    return inst->getStatementID() == CmpStmtID;
  }  
};

class BoolToIntStmt : public Statement {
private:
  Expr* boolExpr;

public:
  BoolToIntStmt(Instruction* instP, Expr* boolExprP) :
    Statement(BoolToIntStmtID, instP), boolExpr(boolExprP) {}
  virtual ~BoolToIntStmt() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BoolToIntStmt* inst) {
    return true;
  }

  static inline bool classof(const Statement* inst) {
    return inst->getStatementID() == BoolToIntStmtID;
  }  
};

class TruncStmt : public Statement {
private:
  Expr* operand;

public:
  TruncStmt(Instruction* instP, Expr* operandP) :
    Statement(TruncStmtID, instP), operand(operandP) {}
  virtual ~TruncStmt() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const TruncStmt* inst) {
    return true;
  }

  static inline bool classof(const Statement* inst) {
    return inst->getStatementID() == TruncStmtID;
  }  
};

class BinaryOperatorStmt : public Statement {
private:
  Expr* left;
  Expr* right;

public:
  BinaryOperatorStmt(Instruction* instP, Expr* leftP, Expr* rightP) :
    Statement(BinaryOperatorStmtID, instP), left(leftP), right(rightP) {}
  virtual ~BinaryOperatorStmt() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BinaryOperatorStmt* inst) {
    return true;
  }

  static inline bool classof(const Statement* inst) {
    return inst->getStatementID() == BinaryOperatorStmtID;
  }  
};

class AllocaStmt : public Statement {
private:
  ConstExpr* typeSize;
  Expr* arraySize;

public:
  AllocaStmt(Instruction* instP, ConstExpr* typeSizeP, Expr* arraySizeP) :
    Statement(AllocaStmtID, instP), typeSize(typeSizeP), arraySize(arraySizeP) {}
  virtual ~AllocaStmt() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const AllocaStmt* inst) {
    return true;
  }

  static inline bool classof(const Statement* inst) {
    return inst->getStatementID() == AllocaStmtID;
  }  
};

class MallocStmt : public Statement {
private:
  Expr* arraySize;
  
public:
  MallocStmt(Instruction* instP, Expr* arraySizeP) :
    Statement(MallocStmtID, instP), arraySize(arraySizeP) {}
  virtual ~MallocStmt() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const MallocStmt* inst) {
    return true;
  }

  static inline bool classof(const Statement* inst) {
    return inst->getStatementID() == MallocStmtID;
  }  
};

class FreeStmt : public Statement {
private:
  Expr* freedPtr;
  
public:
  FreeStmt(Instruction* instP, Expr* freedPtrP) :
    Statement(FreeStmtID, instP), freedPtr(freedPtrP) {}
  virtual ~FreeStmt() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const FreeStmt* inst) {
    return true;
  }

  static inline bool classof(const Statement* inst) {
    return inst->getStatementID() == FreeStmtID;
  }  
};

class AssertStmt : public Statement {
private:
  Expr* assertion;
  
public:
  AssertStmt(Instruction* instP, Expr* assertionP) :
    Statement(AssertStmtID, instP), assertion(assertionP) {}
  virtual ~AssertStmt() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const AssertStmt* inst) {
    return true;
  }

  static inline bool classof(const Statement* inst) {
    return inst->getStatementID() == AssertStmtID;
  }  
};

class AssumeStmt : public Statement {
private:
  Expr* assumption;
  
public:
  AssumeStmt(Instruction* instP, Expr* assumptionP) :
    Statement(AssumeStmtID, instP), assumption(assumptionP) {}
  virtual ~AssumeStmt() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const AssumeStmt* inst) {
    return true;
  }

  static inline bool classof(const Statement* inst) {
    return inst->getStatementID() == AssumeStmtID;
  }  
};

class ReturnStmt : public Statement {
private:
  VarExpr* returnVar;
  Expr* returnValue;
  
public:
  ReturnStmt(Instruction* instP) :
    Statement(ReturnStmtID, instP), returnVar(0), returnValue(0) {}
  ReturnStmt(Instruction* instP, VarExpr* returnVarP, Expr* returnValueP) :
    Statement(ReturnStmtID, instP), returnVar(returnVarP), returnValue(returnValueP) {}
  virtual ~ReturnStmt() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const ReturnStmt* inst) {
    return true;
  }

  static inline bool classof(const Statement* inst) {
    return inst->getStatementID() == ReturnStmtID;
  }  
};

class SelectStmt : public Statement {
private:
  Expr* condition;
  Expr* trueExpr;
  Expr* falseExpr;

public:
  SelectStmt(Instruction* instP, Expr* conditionP, Expr* trueP, Expr* falseP) :
    Statement(SelectStmtID, instP), condition(conditionP), trueExpr(trueP), falseExpr(falseP) {}
  virtual ~SelectStmt() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const SelectStmt* inst) {
    return true;
  }

  static inline bool classof(const Statement* inst) {
    return inst->getStatementID() == SelectStmtID;
  }  
};

}

#endif /*STATEMENTS_H_*/
