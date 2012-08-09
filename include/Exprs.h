//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef EXPRS_H_
#define EXPRS_H_

#include "Expr.h"
#include "Memory.h"

namespace smack {

class MemExpr : public Expr {
private:
  Expr* ptr;
  Memory* mem;
  
public:
  MemExpr(Expr* ptrP, Memory* memP) : Expr(MemExprID), ptr(ptrP), mem(memP) {}
  virtual ~MemExpr() {}
  Expr* getPointer() const;
  Memory* getMemory() const;
  virtual void print(std::ostream &os) const;

  static inline bool classof(const MemExpr* expr) {
    return true;
  }

  static inline bool classof(const Expr* expr) {
    return expr->getExprID() == MemExprID;
  }  
};

class VarExpr : public Expr {
private:
  const Value* var;
  const std::string varName;
  
public:
  VarExpr(const Value* varP) :
    Expr(VarExprID), var(varP), varName("") {}
  VarExpr(const std::string varNameP) :
    Expr(VarExprID), var(0), varName(varNameP) {}
  virtual ~VarExpr() {}
  std::string getName() const;
  virtual void print(std::ostream &os) const;

  static inline bool classof(const VarExpr* expr) {
    return true;
  }

  static inline bool classof(const Expr* expr) {
    return expr->getExprID() == VarExprID;
  }  
};

class ConstExpr : public Expr {
private:
  const Value* constant;
  int64_t intConstant;
  
public:
  ConstExpr(const Value* cons) :
    Expr(ConstantExprID), constant(cons) {}
  ConstExpr(int64_t cons) :
    Expr(ConstantExprID), constant(NULL), intConstant(cons) {}
  virtual ~ConstExpr() {}
  virtual void print(std::ostream &os) const;
  virtual std::string getObjComponent() const;
  virtual std::string getOffComponent() const;

  static inline bool classof(const ConstExpr* expr) {
    return true;
  }

  static inline bool classof(const Expr* expr) {
    return expr->getExprID() == ConstantExprID;
  }  
};

class PtrArithExpr : public Expr {
private:
  Expr* ptr;
  Expr* offset;
  Expr* size;

public:
  PtrArithExpr(Expr* ptrP, Expr* offsetP, Expr* sizeP) :
    Expr(PtrArithExprID), ptr(ptrP), offset(offsetP), size(sizeP) {}
  virtual ~PtrArithExpr() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const PtrArithExpr* expr) {
    return true;
  }

  static inline bool classof(const Expr* expr) {
    return expr->getExprID() == PtrArithExprID;
  }  
};

class NotExpr : public Expr {
private:
  Expr* expr;
  
public:
  NotExpr(Expr* exprP) : Expr(NotExprID), expr(exprP) {}
  virtual ~NotExpr() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const NotExpr* expr) {
    return true;
  }

  static inline bool classof(const Expr* expr) {
    return expr->getExprID() == NotExprID;
  }  
};

class TrueExpr : public Expr {
public:
  TrueExpr() : Expr(TrueExprID) {}
  virtual ~TrueExpr() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const TrueExpr* expr) {
    return true;
  }

  static inline bool classof(const Expr* expr) {
    return expr->getExprID() == TrueExprID;
  }  
};

class FalseExpr : public Expr {
public:
  FalseExpr() : Expr(FalseExprID) {}
  virtual ~FalseExpr() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const FalseExpr* expr) {
    return true;
  }

  static inline bool classof(const Expr* expr) {
    return expr->getExprID() == FalseExprID;
  }  
};

class UndefExpr : public Expr {
public:
  UndefExpr() : Expr(UndefExprID) {}
  virtual ~UndefExpr() {}
  virtual void print(std::ostream &os) const;

  static inline bool classof(const UndefExpr* expr) {
    return true;
  }

  static inline bool classof(const Expr* expr) {
    return expr->getExprID() == UndefExprID;
  }  
};

}

#endif /*EXPRS_H_*/
