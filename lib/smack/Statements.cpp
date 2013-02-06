//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Statements.h"

using namespace smack;
using namespace std;

Expr* AssignStmt::getLeft() const {
  return left;
}

Expr* AssignStmt::getRight() const {
  return right;
}

void AssignStmt::print(ostream &os) const {
  Statement::print(os);
  os << *left << " := " << *right << ";" << endl;
}

const Function* CalledFunction::getCalledFunction() {
  return calledFunction;
}

CallStmt::~CallStmt() {
  for_each(calledFunctions.begin(), calledFunctions.end(), &CalledFunction::destroy);
  calledFunctions.clear();
}

CalledFunction* CallStmt::addCalledFunction(const Function* func) {
  CalledFunction* calledFunction = new CalledFunction(func);
  calledFunctions.push_back(calledFunction);
  return calledFunction;
}

void CallStmt::setReturnVar(VarExpr* returnVarP) {
  returnVar = returnVarP;
}

void CallStmt::addParam(Expr* param) {
  params.push_back(param);
}

void CallStmt::print(ostream &os) const {
  Statement::print(os);
  assert(isa<CallInst>(inst) && "Call instruction has to be CallInst");
  
  if (calledFunctions.empty()) {
    // TODO: this is unsound!
    os << "// Empty call" << endl;
  } else if (calledFunctions.size() == 1) {
    CalledFunction* calledFunc = calledFunctions[0];

    const Function* func = calledFunc->getCalledFunction();
    os << "call ";
    if (returnVar != NULL) {
      os << *returnVar << " := ";
    }    
    string name = translateName(func->getName().str());
    stringstream ps;
    for(vector<Expr*>::const_iterator
        bp = params.begin(), ep = params.end(), p = bp; p != ep; ++p)          
      ps << (p != bp ? "," : "") << *p;
    
    if (name == "__SMACK_record_int")
      os << name << "($off(" << ps.str() << "));" << endl;
    else if (name == "__SMACK_record_obj")
      os << name << "($obj(" << ps.str() << "));" << endl;
    else if (name == "__SMACK_record_ptr")
      os << name << "(" << ps.str() << ");" << endl;
    else
      os << name << "(" << ps.str() << ");" << endl;

  } else {
    unsigned long uniqueLabelSufix = (unsigned long)this;

    os << "goto ";
    int labelCounter = 0;
    for (vector<CalledFunction*>::const_iterator i = calledFunctions.begin(),
        b = calledFunctions.begin(), e = calledFunctions.end(); i != e; ++i, ++labelCounter) {
      if (i != b) {
        os << ", ";
      }
      os << "label_call_" << uniqueLabelSufix << "_" << labelCounter;
    }
    os << ";" << endl;

    labelCounter = 0;
    for (vector<CalledFunction*>::const_iterator i = calledFunctions.begin(),
        e = calledFunctions.end(); i != e; ++i, ++labelCounter) {
      os << "label_call_" << uniqueLabelSufix << "_" << labelCounter << ":" << endl;
      os << "  call ";
      if (returnVar != NULL) {
        os << *returnVar << " := ";
      }
      const Function* func = (*i)->getCalledFunction();
      os << func->getName().str();
      os << "(";
      for(vector<Expr*>::const_iterator
          j = params.begin(), bj = params.begin(), ej = params.end(); j != ej; ++j) {
        if (j != bj) {
          os << ", ";
        }
        os << *j;
      }
      os << ");" << endl;

      os << "  goto label_call_" << uniqueLabelSufix << "_end;" << endl;
    }
    os << "label_call_" << uniqueLabelSufix << "_end:" << endl;
  }
}

void CmpStmt::print(ostream &os) const {
  Statement::print(os);
  assert(inst->hasName() && "Cmp instruction has to have a name");
  assert(isa<ICmpInst>(inst) && "Compare instruction has to be integer compare");
  const ICmpInst* icmp = cast<ICmpInst>(inst);
  os << translateName(icmp->getName().str()) << " := ";
  switch (icmp->getPredicate()) {
  case ICmpInst::ICMP_EQ:
    os << *left << " == " << *right;
    break;
  case ICmpInst::ICMP_NE:
    os << *left << " != " << *right;
    break;
  case ICmpInst::ICMP_SGE:
    os << "$sge($off(" << *left << "), $off(" << *right << "))";
    break;
  case ICmpInst::ICMP_UGE:
    os << "$uge($off(" << *left << "), $off(" << *right << "))";
    break;
  case ICmpInst::ICMP_SLE:
    os << "$sle($off(" << *left << "), $off(" << *right << "))";
    break;
  case ICmpInst::ICMP_ULE:
    os << "$ule($off(" << *left << "), $off(" << *right << "))";
    break;
  case ICmpInst::ICMP_SLT:
    os << "$slt($off(" << *left << "), $off(" << *right << "))";
    break;
  case ICmpInst::ICMP_ULT:
    os << "$ult($off(" << *left << "), $off(" << *right << "))";
    break;
  case ICmpInst::ICMP_SGT:
    os << "$sgt($off(" << *left << "), $off(" << *right << "))";
    break;
  case ICmpInst::ICMP_UGT:
    os << os << "$ugt($off(" << *left << "), $off(" << *right << "))";
    break;
  default:
    assert(false && "Predicate not supported");
  }
  os << ";" << endl;
}

void BoolToIntStmt::print(ostream &os) const {
  Statement::print(os);
  assert(inst->hasName() && "BoolToInt instruction has to have a name");
  os << translateName(inst->getName().str()) 
     << " := $b2p(" << *boolExpr << ");" << endl;
}

void TruncStmt::print(ostream &os) const {
  Statement::print(os);
  assert(inst->hasName() && "Trunc instruction has to have a name");
  os << translateName(inst->getName().str())  << " := ";
  if (((TruncInst *) inst)->getDestTy()->isIntegerTy(1))
    os << "$p2b";
  else
    os << "$trunc";
  os << "(" << *operand << ");" << endl;
}

void BinaryOperatorStmt::print(ostream &os) const {
  Statement::print(os);
  assert(inst->hasName() && "BinaryOperator instruction has to have a name");
  assert(isa<BinaryOperator>(inst) && "Binary operator instruction has to be BinaryOperator");
  os << translateName(inst->getName().str()) << " := ";

  if (inst->getType()->isIntegerTy(1))
    os << "$i2b(";
  else
    os << "$ptr($NULL, ";
  
  switch (inst->getOpcode()) {
  case Instruction::Add:
    os << "$add";
    break;
  case Instruction::Sub:
    os << "$sub";
    break;
  case Instruction::Mul:
    os << "$mul";
    break;
  case Instruction::SDiv:
    os << "$sdiv";
    break;
  case Instruction::UDiv:
    os << "$udiv";
    break;
  case Instruction::SRem:
    os << "$srem";
    break;
  case Instruction::URem:
    os << "$urem";
    break;
  case Instruction::And:
    os << "$and";
    break;
  case Instruction::Or:
    os << "$or";
    break;
  case Instruction::Xor:
    os << "$xor";
    break;
  case Instruction::LShr:
    os << "$lshr";
    break;
  case Instruction::AShr:
    os << "$ashr";
    break;
  case Instruction::Shl:
    os << "$shl";
    break;
  default:
    assert(false && "Predicate not supported");
  }
  os << "( ";
  if (inst->getOperand(0)->getType()->isIntegerTy(1))
    os << "$b2i(";
  else 
    os << "$off(";
  os << *left << "), ";

  if (inst->getOperand(1)->getType()->isIntegerTy(1))
    os << "$b2i(";
  else 
    os << "$off(";
  os << *right << ")";
  
  os << " ));" << endl;
}

void AllocaStmt::print(ostream &os) const {
  Statement::print(os);
  assert(inst->hasName() && "Alloca instruction has to have a name");
  string varName = translateName(inst->getName().str());
  
  os << "call " << varName << " := ";
  os << "$alloca($mul(" << typeSize->getOffComponent() << ", " << arraySize->getOffComponent() << "));" << endl;
}

void MallocStmt::print(ostream &os) const {
  Statement::print(os);
  assert(inst->hasName() && "Malloc instruction has to have a name");
  string varName = translateName(inst->getName().str());
  
  os << "call " << varName << " := ";
  os << "$malloc(" << arraySize->getOffComponent() << ");" << endl;
}

void FreeStmt::print(ostream &os) const {
  Statement::print(os);
  os << "call $free(" << *freedPtr << ");" << endl;
}

void AssertStmt::print(ostream &os) const {
  Statement::print(os);
  os << "assert(" << *assertion << " != $ptr($NULL, " << Common::int_const(0) << "));" << endl;
}

void AssumeStmt::print(ostream &os) const {
  Statement::print(os);
  os << "assume(" << *assumption << " != $ptr($NULL, " << Common::int_const(0) << "));" << endl;
}

void ReturnStmt::print(ostream &os) const {
  Statement::print(os);
  if (returnValue != NULL) {
    assert(returnVar != NULL && "Return variable shouldn't be NULL");
    os << *returnVar << " := " << *returnValue << ";" << endl << "  ";
  }
  os << "return;" << endl;
}

void SelectStmt::print(ostream &os) const {
  Statement::print(os);
  assert(inst->hasName() && "Select instruction has to have a name");
  os << "if (" << *condition << ") {" << endl;
  os << "    " << translateName(inst->getName().str()) << " := " << *trueExpr << ";" << endl;
  os << "  } else {" << endl;
  os << "    " << translateName(inst->getName().str()) << " := " << *falseExpr << ";" << endl;
  os << "  }" << endl;
}
