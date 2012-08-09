//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLINSTRUCTIONS_H_
#define BPLINSTRUCTIONS_H_

#include "BPLInstruction.h"

namespace smack {

class BPLAssignInst : public BPLInstruction {
private:
  Expr* left;
  Expr* right;

public:
  BPLAssignInst(Instruction* instP, Expr* leftP, Expr* rightP) :
    BPLInstruction(BPLAssignInstID, instP), left(leftP), right(rightP) {}
  virtual ~BPLAssignInst() {}
  Expr* getLeft() const;
  Expr* getRight() const;
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLAssignInst* inst) {
    return true;
  }

  static inline bool classof(const BPLInstruction* inst) {
    return inst->getBPLInstructionID() == BPLAssignInstID;
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

class BPLCallInst : public BPLInstruction {
private:
  std::vector<CalledFunction*> calledFunctions;
  VarExpr* returnVar;
  std::vector<Expr*> params;

public:
  BPLCallInst(Instruction* instP) : BPLInstruction(BPLCallInstID, instP), returnVar(NULL) {}
  virtual ~BPLCallInst();
  CalledFunction* addCalledFunction(const Function* func);
  void setReturnVar(VarExpr* returnVarP);
  void addParam(Expr* param);
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLCallInst* inst) {
    return true;
  }

  static inline bool classof(const BPLInstruction* inst) {
    return inst->getBPLInstructionID() == BPLCallInstID;
  }  
};

class BPLCmpInst : public BPLInstruction {
private:
  Expr* left;
  Expr* right;

public:
  BPLCmpInst(Instruction* instP, Expr* leftP, Expr* rightP) :
    BPLInstruction(BPLCmpInstID, instP), left(leftP), right(rightP) {}
  virtual ~BPLCmpInst() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLCmpInst* inst) {
    return true;
  }

  static inline bool classof(const BPLInstruction* inst) {
    return inst->getBPLInstructionID() == BPLCmpInstID;
  }  
};

class BPLBoolToIntInst : public BPLInstruction {
private:
  Expr* boolExpr;

public:
  BPLBoolToIntInst(Instruction* instP, Expr* boolExprP) :
    BPLInstruction(BPLBoolToIntInstID, instP), boolExpr(boolExprP) {}
  virtual ~BPLBoolToIntInst() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLBoolToIntInst* inst) {
    return true;
  }

  static inline bool classof(const BPLInstruction* inst) {
    return inst->getBPLInstructionID() == BPLBoolToIntInstID;
  }  
};

class BPLTruncInst : public BPLInstruction {
private:
  Expr* operand;

public:
  BPLTruncInst(Instruction* instP, Expr* operandP) :
    BPLInstruction(BPLTruncInstID, instP), operand(operandP) {}
  virtual ~BPLTruncInst() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLTruncInst* inst) {
    return true;
  }

  static inline bool classof(const BPLInstruction* inst) {
    return inst->getBPLInstructionID() == BPLTruncInstID;
  }  
};

class BPLBinaryOperatorInst : public BPLInstruction {
private:
  Expr* left;
  Expr* right;

public:
  BPLBinaryOperatorInst(Instruction* instP, Expr* leftP, Expr* rightP) :
    BPLInstruction(BPLBinaryOperatorInstID, instP), left(leftP), right(rightP) {}
  virtual ~BPLBinaryOperatorInst() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLBinaryOperatorInst* inst) {
    return true;
  }

  static inline bool classof(const BPLInstruction* inst) {
    return inst->getBPLInstructionID() == BPLBinaryOperatorInstID;
  }  
};

class BPLAllocaInst : public BPLInstruction {
private:
  ConstExpr* typeSize;
  Expr* arraySize;

public:
  BPLAllocaInst(Instruction* instP, ConstExpr* typeSizeP, Expr* arraySizeP) :
    BPLInstruction(BPLAllocaInstID, instP), typeSize(typeSizeP), arraySize(arraySizeP) {}
  virtual ~BPLAllocaInst() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLAllocaInst* inst) {
    return true;
  }

  static inline bool classof(const BPLInstruction* inst) {
    return inst->getBPLInstructionID() == BPLAllocaInstID;
  }  
};

class BPLMallocInst : public BPLInstruction {
private:
  Expr* arraySize;
  
public:
  BPLMallocInst(Instruction* instP, Expr* arraySizeP) :
    BPLInstruction(BPLMallocInstID, instP), arraySize(arraySizeP) {}
  virtual ~BPLMallocInst() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLMallocInst* inst) {
    return true;
  }

  static inline bool classof(const BPLInstruction* inst) {
    return inst->getBPLInstructionID() == BPLMallocInstID;
  }  
};

class BPLFreeInst : public BPLInstruction {
private:
  Expr* freedPtr;
  
public:
  BPLFreeInst(Instruction* instP, Expr* freedPtrP) :
    BPLInstruction(BPLFreeInstID, instP), freedPtr(freedPtrP) {}
  virtual ~BPLFreeInst() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLFreeInst* inst) {
    return true;
  }

  static inline bool classof(const BPLInstruction* inst) {
    return inst->getBPLInstructionID() == BPLFreeInstID;
  }  
};

class BPLAssertInst : public BPLInstruction {
private:
  Expr* assertion;
  
public:
  BPLAssertInst(Instruction* instP, Expr* assertionP) :
    BPLInstruction(BPLAssertInstID, instP), assertion(assertionP) {}
  virtual ~BPLAssertInst() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLAssertInst* inst) {
    return true;
  }

  static inline bool classof(const BPLInstruction* inst) {
    return inst->getBPLInstructionID() == BPLAssertInstID;
  }  
};

class BPLAssumeInst : public BPLInstruction {
private:
  Expr* assumption;
  
public:
  BPLAssumeInst(Instruction* instP, Expr* assumptionP) :
    BPLInstruction(BPLAssumeInstID, instP), assumption(assumptionP) {}
  virtual ~BPLAssumeInst() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLAssumeInst* inst) {
    return true;
  }

  static inline bool classof(const BPLInstruction* inst) {
    return inst->getBPLInstructionID() == BPLAssumeInstID;
  }  
};

class BPLReturnInst : public BPLInstruction {
private:
  VarExpr* returnVar;
  Expr* returnValue;
  
public:
  BPLReturnInst(Instruction* instP) :
    BPLInstruction(BPLReturnInstID, instP), returnVar(0), returnValue(0) {}
  BPLReturnInst(Instruction* instP, VarExpr* returnVarP, Expr* returnValueP) :
    BPLInstruction(BPLReturnInstID, instP), returnVar(returnVarP), returnValue(returnValueP) {}
  virtual ~BPLReturnInst() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLReturnInst* inst) {
    return true;
  }

  static inline bool classof(const BPLInstruction* inst) {
    return inst->getBPLInstructionID() == BPLReturnInstID;
  }  
};

class BPLSelectInst : public BPLInstruction {
private:
  Expr* condition;
  Expr* trueExpr;
  Expr* falseExpr;

public:
  BPLSelectInst(Instruction* instP, Expr* conditionP, Expr* trueP, Expr* falseP) :
    BPLInstruction(BPLSelectInstID, instP), condition(conditionP), trueExpr(trueP), falseExpr(falseP) {}
  virtual ~BPLSelectInst() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLSelectInst* inst) {
    return true;
  }

  static inline bool classof(const BPLInstruction* inst) {
    return inst->getBPLInstructionID() == BPLSelectInstID;
  }  
};

}

#endif /*BPLINSTRUCTIONS_H_*/
