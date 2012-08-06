//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "BPLExprs.h"

using namespace smack;

BPLExpr* BPLMemExpr::getPointer() const {
  return ptr;
}

Memory* BPLMemExpr::getMemory() const {
  return mem;
}

void BPLMemExpr::print(std::ostream &os) const {
  os << *mem << "[" << *ptr << "]";
}

std::string BPLVarExpr::getName() const {
  return varName;
}

void BPLVarExpr::print(std::ostream &os) const {
  if (var == 0) {
    assert(!varName.empty() && "If var is NULL, varName shouldn't be empty");
    os << varName;
  } else {
    assert(varName.empty() && "If var is not NULL, varName should be empty");
    assert(var->hasName() && "Variable has to have a name");
    os << translateName(var);
  }
}

void BPLConstantExpr::print(std::ostream &os) const {
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
          os << "Ptr(null, 0-" << stringValue.substr(1) << ")";
        } else {
          os << "Ptr(null, " << stringValue << ")";
        }
      }
    } else if (isa<ConstantPointerNull>(constant)) {
      os << "Ptr(null, 0)";
    } else {
      assert(false && "Value type not supported");
    }
  } else {
    os << "Ptr(null, " << intConstant << ")";
  }
}

std::string BPLConstantExpr::getObjComponent() const {
  std::stringstream obj;
  obj << "null";
  return obj.str();
}

std::string BPLConstantExpr::getOffComponent() const {
  std::stringstream off;
  if (constant != NULL) {
    if (const ConstantInt* ci = dyn_cast<ConstantInt>(constant)) {
      const APInt& intValue = ci->getValue();
      std::string stringValue = intValue.toString(10, true);
      if (intValue.isNegative()) {
        off << "0-" << stringValue.substr(1);
      } else {
        off << stringValue;
      }
    } else if (isa<ConstantPointerNull>(constant)) {
      off << "0";
    } else {
      assert(false && "Value type not supported");
    }
  } else {
    off << intConstant;
  }
  return off.str();
}

void BPLPtrArithExpr::print(std::ostream &os) const {
  os << "__SMACK_PtrArith(" << *ptr << ", " << offset->getOffComponent() << ", " << size->getOffComponent() << ")";
}

void BPLNotExpr::print(std::ostream &os) const {
  os << "!(" << *expr << ")";
}

void BPLTrueExpr::print(std::ostream &os) const {
  os << "true";
}

void BPLFalseExpr::print(std::ostream &os) const {
  os << "false";
}

void BPLUndefExpr::print(std::ostream &os) const {
  os << "undef";
}
