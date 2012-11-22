//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Exprs.h"
#include "Common.h"

using namespace smack;

Expr* MemExpr::getPointer() const {
  return ptr;
}

Memory* MemExpr::getMemory() const {
  return mem;
}

void MemExpr::print(std::ostream &os) const {
  os << *mem << "[" << *ptr << "]";
}

std::string VarExpr::getName() const {
  return varName;
}

void VarExpr::print(std::ostream &os) const {
  if (var == 0) {
    assert(!varName.empty() && "If var is NULL, varName shouldn't be empty");
    os << varName;
  } else {
    assert(varName.empty() && "If var is not NULL, varName should be empty");
    assert(var->hasName() && "Variable has to have a name");
    os << translateName(var);
  }
}

void ConstExpr::print(std::ostream &os) const {
  if (constant != NULL) {
    if (const ConstantInt* ci = dyn_cast<ConstantInt>(constant)) {
      if (ci->getBitWidth() == 1) {
        if (ci->isZero()) {
          os << "false";
        } else {
          os << "true";
        }
      } else {
        
        std::string sval = Common::int_const( ci->getLimitedValue() );
        if ( ci->isNegative() )
          os << "Ptr(null,sub(" << Common::int_const(0) << "," << sval.substr(1) << "))";
        else
          os << "Ptr(null," << sval << ")";
      }
    } else if (isa<ConstantPointerNull>(constant)) {
      os << "Ptr(null," << Common::int_const(0) << ")";
    } else {
      assert(false && "Value type not supported");
    }
  } else {
    os << "Ptr(null," << Common::int_const(intConstant) << ")";
  }
}

std::string ConstExpr::getObjComponent() const {
  std::stringstream obj;
  obj << "null";
  return obj.str();
}

std::string ConstExpr::getOffComponent() const {
  std::stringstream off;
  if (constant != NULL) {
    if (const ConstantInt* ci = dyn_cast<ConstantInt>(constant)) {
      std::string sval = Common::int_const( ci->getLimitedValue() );
      if ( ci->isNegative() ) {
        off << "sub(" << Common::int_const(0) << ", " << sval.substr(1) << ")";
      } else {
        off << sval;
      }
    } else if (isa<ConstantPointerNull>(constant)) {
      off << Common::int_const(0);
    } else {
      assert(false && "Value type not supported");
    }
  } else {
    off << Common::int_const(intConstant);
  }
  return off.str();
}

void PtrArithExpr::print(std::ostream &os) const {
  os << "__SMACK_PtrArith(" << *ptr << ", " << offset->getOffComponent() << ", " << size->getOffComponent() << ")";
}

void NotExpr::print(std::ostream &os) const {
  os << "!(" << *expr << ")";
}

void TrueExpr::print(std::ostream &os) const {
  os << "true";
}

void FalseExpr::print(std::ostream &os) const {
  os << "false";
}

void UndefExpr::print(std::ostream &os) const {
  os << "undef";
}
