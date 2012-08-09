//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLEXPR_H_
#define BPLEXPR_H_

#include "BPLPrintUtils.h"
#include "llvm/Constants.h"
#include "llvm/Instructions.h"
#include "llvm/Support/Debug.h"
#include <sstream>

#undef DEBUG_TYPE
#define DEBUG_TYPE "smack"

using namespace llvm;

namespace smack {

class BPLExpr {
public:
  enum BPLExprIDs {
    BPLMemExprID,
    BPLVarExprID,
    BPLConstantExprID,
    BPLPtrArithExprID,
    BPLNotExprID,
    BPLTrueExprID,
    BPLFalseExprID,
    BPLUndefExprID
  };

private:
  BPLExprIDs id;
  
public:
  BPLExpr(BPLExprIDs idP) : id(idP) {}
  virtual ~BPLExpr() {}
  virtual void print(std::ostream &os) const = 0;
  
  virtual std::string getObjComponent() const {
    std::stringstream obj;
    obj << "Obj(";
    print(obj);
    obj << ")";
    return obj.str();
  }
  
  virtual std::string getOffComponent() const {
    std::stringstream off;
    off << "Off(";
    print(off);
    off << ")";
    return off.str();
  }
  
  inline BPLExprIDs getBPLExprID() const {
    return id;
  }
  
  static inline bool classof(const BPLExpr* expr) {
    return true;
  }
};
std::ostream &operator<<(std::ostream &os, const BPLExpr* expr);
std::ostream &operator<<(std::ostream &os, const BPLExpr& expr);

}

#endif /*BPLEXPR_H_*/
