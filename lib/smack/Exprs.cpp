//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Exprs.h"

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
        const APInt& intValue = ci->getValue();
        std::string stringValue = intValue.toString(10, true);
        if (intValue.isNegative()) {
          os << "Ptr(null, sub(0bv32, " << stringValue.substr(1) << "bv32))";
        } else {
          os << "Ptr(null, " << stringValue << "bv32)";
        }
      }
    } else if (isa<ConstantPointerNull>(constant)) {
      os << "Ptr(null, 0bv32)";
    } else {
      assert(false && "Value type not supported");
    }
  } else {
    os << "Ptr(null, " << intConstant << "bv32)";
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
      const APInt& intValue = ci->getValue();
      std::string stringValue = intValue.toString(10, true);
      if (intValue.isNegative()) {
        off << "sub(0bv32, " << stringValue.substr(1) << "bv32)";
      } else {
        off << stringValue << "bv32";
      }
    } else if (isa<ConstantPointerNull>(constant)) {
      off << "0bv32";
    } else {
      assert(false && "Value type not supported");
    }
  } else {
    off << intConstant << "bv32";
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
