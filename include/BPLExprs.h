//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLEXPRS_H_
#define BPLEXPRS_H_

#include "BPLExpr.h"
#include "Memory.h"

namespace smack {

class BPLMemExpr : public BPLExpr {
private:
  BPLExpr* ptr;
  Memory* mem;
  
public:
  BPLMemExpr(BPLExpr* ptrP, Memory* memP) : BPLExpr(BPLMemExprID), ptr(ptrP), mem(memP) {}
  virtual ~BPLMemExpr() {}
  BPLExpr* getPointer() const;
  Memory* getMemory() const;
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLMemExpr* expr) {
    return true;
  }

  static inline bool classof(const BPLExpr* expr) {
    return expr->getBPLExprID() == BPLMemExprID;
  }  
};

class BPLVarExpr : public BPLExpr {
private:
  const Value* var;
  const std::string varName;
  
public:
  BPLVarExpr(const Value* varP) :
    BPLExpr(BPLVarExprID), var(varP), varName("") {}
  BPLVarExpr(const std::string varNameP) :
    BPLExpr(BPLVarExprID), var(0), varName(varNameP) {}
  virtual ~BPLVarExpr() {}
  std::string getName() const;
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLVarExpr* expr) {
    return true;
  }

  static inline bool classof(const BPLExpr* expr) {
    return expr->getBPLExprID() == BPLVarExprID;
  }  
};

class BPLConstantExpr : public BPLExpr {
private:
  const Value* constant;
  int64_t intConstant;
  
public:
  BPLConstantExpr(const Value* cons) :
    BPLExpr(BPLConstantExprID), constant(cons) {}
  BPLConstantExpr(int64_t cons) :
    BPLExpr(BPLConstantExprID), constant(NULL), intConstant(cons) {}
  virtual ~BPLConstantExpr() {}
  virtual void print(std::ostream &os) const;
  virtual std::string getObjComponent() const;
  virtual std::string getOffComponent() const;

  static inline bool classof(const BPLConstantExpr* expr) {
    return true;
  }

  static inline bool classof(const BPLExpr* expr) {
    return expr->getBPLExprID() == BPLConstantExprID;
  }  
};

class BPLPtrArithExpr : public BPLExpr {
private:
  BPLExpr* ptr;
  BPLExpr* offset;
  BPLExpr* size;

public:
  BPLPtrArithExpr(BPLExpr* ptrP, BPLExpr* offsetP, BPLExpr* sizeP) :
    BPLExpr(BPLPtrArithExprID), ptr(ptrP), offset(offsetP), size(sizeP) {}
  virtual ~BPLPtrArithExpr() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLPtrArithExpr* expr) {
    return true;
  }

  static inline bool classof(const BPLExpr* expr) {
    return expr->getBPLExprID() == BPLPtrArithExprID;
  }  
};

class BPLNotExpr : public BPLExpr {
private:
  BPLExpr* expr;
  
public:
  BPLNotExpr(BPLExpr* exprP) : BPLExpr(BPLNotExprID), expr(exprP) {}
  virtual ~BPLNotExpr() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLNotExpr* expr) {
    return true;
  }

  static inline bool classof(const BPLExpr* expr) {
    return expr->getBPLExprID() == BPLNotExprID;
  }  
};

class BPLTrueExpr : public BPLExpr {
public:
  BPLTrueExpr() : BPLExpr(BPLTrueExprID) {}
  virtual ~BPLTrueExpr() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLTrueExpr* expr) {
    return true;
  }

  static inline bool classof(const BPLExpr* expr) {
    return expr->getBPLExprID() == BPLTrueExprID;
  }  
};

class BPLFalseExpr : public BPLExpr {
public:
  BPLFalseExpr() : BPLExpr(BPLFalseExprID) {}
  virtual ~BPLFalseExpr() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLFalseExpr* expr) {
    return true;
  }

  static inline bool classof(const BPLExpr* expr) {
    return expr->getBPLExprID() == BPLFalseExprID;
  }  
};

class BPLUndefExpr : public BPLExpr {
public:
  BPLUndefExpr() : BPLExpr(BPLUndefExprID) {}
  virtual ~BPLUndefExpr() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const BPLUndefExpr* expr) {
    return true;
  }

  static inline bool classof(const BPLExpr* expr) {
    return expr->getBPLExprID() == BPLUndefExprID;
  }  
};

}

#endif /*BPLEXPRS_H_*/
