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
  BPLExpr* left;
  BPLExpr* right;

public:
  BPLAssignInst(Instruction* instP, BPLExpr* leftP, BPLExpr* rightP) :
    BPLInstruction(BPLAssignInstID, instP), left(leftP), right(rightP) {}
  virtual ~BPLAssignInst() {}
  BPLExpr* getLeft() const;
  BPLExpr* getRight() const;
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
  BPLVarExpr* returnVar;
  std::vector<BPLExpr*> params;

public:
  BPLCallInst(Instruction* instP) : BPLInstruction(BPLCallInstID, instP), returnVar(NULL) {}
  virtual ~BPLCallInst();
  CalledFunction* addCalledFunction(const Function* func);
  void setReturnVar(BPLVarExpr* returnVarP);
  void addParam(BPLExpr* param);
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
  BPLExpr* left;
  BPLExpr* right;

public:
  BPLCmpInst(Instruction* instP, BPLExpr* leftP, BPLExpr* rightP) :
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
  BPLExpr* boolExpr;

public:
  BPLBoolToIntInst(Instruction* instP, BPLExpr* boolExprP) :
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
  BPLExpr* operand;

public:
  BPLTruncInst(Instruction* instP, BPLExpr* operandP) :
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
  BPLExpr* left;
  BPLExpr* right;

public:
  BPLBinaryOperatorInst(Instruction* instP, BPLExpr* leftP, BPLExpr* rightP) :
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
  BPLConstantExpr* typeSize;
  BPLExpr* arraySize;

public:
  BPLAllocaInst(Instruction* instP, BPLConstantExpr* typeSizeP, BPLExpr* arraySizeP) :
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
  BPLExpr* arraySize;
  
public:
  BPLMallocInst(Instruction* instP, BPLExpr* arraySizeP) :
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
  BPLExpr* freedPtr;
  
public:
  BPLFreeInst(Instruction* instP, BPLExpr* freedPtrP) :
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
  BPLExpr* assertion;
  
public:
  BPLAssertInst(Instruction* instP, BPLExpr* assertionP) :
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
  BPLExpr* assumption;
  
public:
  BPLAssumeInst(Instruction* instP, BPLExpr* assumptionP) :
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
  BPLVarExpr* returnVar;
  BPLExpr* returnValue;
  
public:
  BPLReturnInst(Instruction* instP) :
    BPLInstruction(BPLReturnInstID, instP), returnVar(0), returnValue(0) {}
  BPLReturnInst(Instruction* instP, BPLVarExpr* returnVarP, BPLExpr* returnValueP) :
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
  BPLExpr* condition;
  BPLExpr* trueExpr;
  BPLExpr* falseExpr;

public:
  BPLSelectInst(Instruction* instP, BPLExpr* conditionP, BPLExpr* trueP, BPLExpr* falseP) :
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
