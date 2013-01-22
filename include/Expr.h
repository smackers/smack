//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef EXPR_H_
#define EXPR_H_

#include "BplPrintUtils.h"
#include "llvm/Constants.h"
#include "llvm/Instructions.h"
#include "llvm/Support/Debug.h"
#include <sstream>

#undef DEBUG_TYPE
#define DEBUG_TYPE "smack"

using namespace llvm;

namespace smack {

class Expr {
public:
  enum ExprIDs {
    MemExprID,
    VarExprID,
    ConstantExprID,
    PtrArithExprID,
    NotExprID,
    TrueExprID,
    FalseExprID,
    UndefExprID
  };

private:
  ExprIDs id;
  
public:
  Expr(ExprIDs idP) : id(idP) {}
  virtual ~Expr() {}
  virtual void print(std::ostream &os) const = 0;
  
  virtual std::string getObjComponent() const {
    std::stringstream obj;
    obj << "$obj(";
    print(obj);
    obj << ")";
    return obj.str();
  }
  
  virtual std::string getOffComponent() const {
    std::stringstream off;
    off << "$off(";
    print(off);
    off << ")";
    return off.str();
  }
  
  inline ExprIDs getExprID() const {
    return id;
  }
  
  static inline bool classof(const Expr* expr) {
    return true;
  }
};
std::ostream &operator<<(std::ostream &os, const Expr* expr);
std::ostream &operator<<(std::ostream &os, const Expr& expr);

}

#endif /*EXPR_H_*/
