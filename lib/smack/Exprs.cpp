//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Exprs.h"
#include "Common.h"

using namespace smack;
using namespace std;

Expr* MemExpr::getPointer() const {
  return ptr;
}

Memory* MemExpr::getMemory() const {
  return mem;
}

void MemExpr::print(ostream &os) const {
  os << *mem << "[" << *ptr << "]";
}

string VarExpr::getName() const {
  return varName;
}

void VarExpr::print(ostream &os) const {
  if (var == 0) {
    assert(!varName.empty() && "If var is NULL, varName shouldn't be empty");
    os << varName;
  } else {
    assert(varName.empty() && "If var is not NULL, varName should be empty");
    assert(var->hasName() && "Variable has to have a name");
    os << translateName(var);
  }
}

void ConstExpr::print(ostream &os) const {
  if (constant != NULL) {
    if (const ConstantInt* ci = dyn_cast<ConstantInt>(constant)) {
      if (ci->getBitWidth() == 1) {
        if (ci->isZero())
          os << "false";
        else
          os << "true";
      } else        
        os << "$ptr($NULL," << Common::int_const( ci->getValue() ) <<  ")";

    } else if (isa<ConstantPointerNull>(constant)) {
      os << "$ptr($NULL," << Common::int_const(0) << ")";
    } else if (isa<Function>(constant)) {
      std::string funcName = strip(constant->getName().str());
      os << funcName << "#ptr";
    } else {
      assert(false && "Value type not supported");
    }
  } else {
    os << "$ptr($NULL," << Common::int_const(intConstant) << ")";
  }
}

string ConstExpr::getObjComponent() const {
  stringstream obj;
  obj << "$NULL";
  return obj.str();
}

string ConstExpr::getOffComponent() const {
  stringstream off;
  if (constant != NULL) {
    if (const ConstantInt* ci = dyn_cast<ConstantInt>(constant)) {
      string sval = Common::int_const( ci->getLimitedValue() );
      if ( ci->isNegative() ) {
        off << "$sub(" << Common::int_const(0) << ", " << sval.substr(1) << ")";
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

void PtrArithExpr::print(ostream &os) const {
  os << "$pa(" << *ptr << ", " 
     << offset->getOffComponent() << ", " 
     << size->getOffComponent() << ")";
}

void NotExpr::print(ostream &os) const {
  os << "!(" << *expr << ")";
}

void TrueExpr::print(ostream &os) const {
  os << "true";
}

void FalseExpr::print(ostream &os) const {
  os << "false";
}

void UndefExpr::print(ostream &os) const {
  os << "$UNDEF";
}
