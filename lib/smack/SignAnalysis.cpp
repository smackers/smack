//
// This file is distributed under the MIT License. See LICENSE for details.
//

//
// This pass infers the sign (signed / unsigned) of integer SSA values
// via bidirectional dataflow analysis over a four-point lattice:
//
//        Unknown
//        /     \;
//    Signed   Unsigned
//        \     /
//        Conflict
//
// Constraints are drawn from operations that carry explicit sign intent
// (sdiv, zext, signed comparisons, etc.) and from nsw/nuw flags on
// otherwise sign-agnostic arithmetic.  Memory propagation uses sea-dsa
// alias information to connect stores to loads.  The analysis iterates
// to a fixpoint.
//

#define DEBUG_TYPE "smack-sign"
#include "smack/SignAnalysis.h"
#include "seadsa/Graph.hh"
#include "smack/DSAWrapper.h"
#include "smack/Debug.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

namespace smack {

using namespace llvm;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

static const char *signName(Sign S) {
  switch (S) {
  case Sign::Unknown:
    return "unknown";
  case Sign::Signed:
    return "signed";
  case Sign::Unsigned:
    return "unsigned";
  case Sign::Conflict:
    return "conflict";
  }
  return "?";
}

/// Return true if V is an integer (not pointer, not void, not FP).
static bool isInteger(const Value *V) { return V->getType()->isIntegerTy(); }

/// Classify the nsw/nuw flags on an OverflowingBinaryOperator.
/// Returns Signed if nsw-only, Unsigned if nuw-only, Unknown otherwise.
static Sign flagSign(const Instruction &I) {
  if (auto *OBO = dyn_cast<OverflowingBinaryOperator>(&I)) {
    bool nsw = OBO->hasNoSignedWrap();
    bool nuw = OBO->hasNoUnsignedWrap();
    if (nsw && !nuw)
      return Sign::Signed;
    if (nuw && !nsw)
      return Sign::Unsigned;
  }
  return Sign::Unknown;
}

// ---------------------------------------------------------------------------
// SignAnalysis implementation
// ---------------------------------------------------------------------------

char SignAnalysis::ID = 0;

StringRef SignAnalysis::getPassName() const {
  return "Integer sign inference analysis";
}

void SignAnalysis::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<DSAWrapper>();
}

bool SignAnalysis::update(const Value *V, Sign S) {
  if (S == Sign::Unknown)
    return false;
  auto it = SignMap.find(V);
  if (it == SignMap.end()) {
    SignMap[V] = S;
    return true;
  }
  Sign old = it->second;
  Sign merged = meetSign(old, S);
  if (merged == old)
    return false;
  it->second = merged;
  return true;
}

Sign SignAnalysis::getSign(const Value *V) const {
  auto it = SignMap.find(V);
  return it != SignMap.end() ? it->second : Sign::Unknown;
}

// ---------------------------------------------------------------------------
// Memory index (DSA-based)
// ---------------------------------------------------------------------------

SignAnalysis::MemCell SignAnalysis::resolvePointer(const Value *Ptr) {
  if (!DSA)
    return {nullptr, 0};
  auto *node = DSA->getNode(Ptr);
  if (!node)
    return {nullptr, 0};
  // Skip incomplete/complicated nodes — too imprecise for sign propagation
  if (node->isIncomplete() || node->isExternal() || node->isIntToPtr() ||
      node->isPtrToInt() || node->isUnknown())
    return {nullptr, 0};
  unsigned offset = DSA->getOffset(Ptr);
  // Normalize offset for collapsed nodes
  if (node->isOffsetCollapsed())
    offset = 0;
  return {node, offset};
}

void SignAnalysis::buildMemoryIndex(Module &M) {
  CellStores.clear();
  CellLoads.clear();
  for (auto &F : M) {
    for (auto &I : instructions(F)) {
      if (auto *SI = dyn_cast<StoreInst>(&I)) {
        if (!isInteger(SI->getValueOperand()))
          continue;
        auto cell = resolvePointer(SI->getPointerOperand());
        if (cell.first)
          CellStores[cell].push_back(SI->getValueOperand());
      } else if (auto *LI = dyn_cast<LoadInst>(&I)) {
        if (!isInteger(LI))
          continue;
        auto cell = resolvePointer(LI->getPointerOperand());
        if (cell.first)
          CellLoads[cell].push_back(LI);
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Forward propagation: def → result
// ---------------------------------------------------------------------------

bool SignAnalysis::propagateForward(Instruction &I) {
  if (!isInteger(&I))
    return false;

  bool changed = false;

  switch (I.getOpcode()) {
  // Cast instructions that determine result sign
  case Instruction::SExt:
  case Instruction::FPToSI:
    changed |= update(&I, Sign::Signed);
    break;
  case Instruction::ZExt:
  case Instruction::FPToUI:
    changed |= update(&I, Sign::Unsigned);
    break;

  // Trunc: propagate sign of the source operand through
  case Instruction::Trunc:
    changed |= update(&I, getSign(I.getOperand(0)));
    break;

  // PHI: meet over all incoming values
  case Instruction::PHI: {
    auto &Phi = cast<PHINode>(I);
    Sign S = Sign::Unknown;
    for (unsigned i = 0, e = Phi.getNumIncomingValues(); i < e; ++i)
      S = meetSign(S, getSign(Phi.getIncomingValue(i)));
    changed |= update(&I, S);
    break;
  }

  // Select: meet of true and false values
  case Instruction::Select:
    changed |= update(
        &I, meetSign(getSign(I.getOperand(1)), getSign(I.getOperand(2))));
    break;

  // Signed arithmetic results
  case Instruction::SDiv:
  case Instruction::SRem:
  case Instruction::AShr:
    changed |= update(&I, Sign::Signed);
    break;

  // Unsigned arithmetic results
  case Instruction::UDiv:
  case Instruction::URem:
  case Instruction::LShr:
    changed |= update(&I, Sign::Unsigned);
    break;

  // Load: propagate from aliasing stores
  case Instruction::Load: {
    auto *LI = cast<LoadInst>(&I);
    auto cell = resolvePointer(LI->getPointerOperand());
    if (cell.first) {
      auto it = CellStores.find(cell);
      if (it != CellStores.end()) {
        for (auto *storedVal : it->second)
          changed |= update(&I, getSign(storedVal));
      }
    }
    break;
  }

  // Call: propagate actual argument signs → formal parameters;
  //       propagate callee return value sign → CallInst result
  case Instruction::Call:
  case Instruction::Invoke: {
    auto *CB = cast<CallBase>(&I);
    Function *callee = CB->getCalledFunction();
    if (!callee || callee->isDeclaration())
      break;
    // Actual args → formal params
    for (unsigned i = 0, e = CB->arg_size(); i < e && i < callee->arg_size();
         ++i) {
      if (isInteger(CB->getArgOperand(i)))
        changed |= update(callee->getArg(i), getSign(CB->getArgOperand(i)));
    }
    // Return value → CallInst result
    if (isInteger(CB)) {
      for (auto &BB : *callee) {
        if (auto *RI = dyn_cast<ReturnInst>(BB.getTerminator())) {
          if (RI->getReturnValue() && isInteger(RI->getReturnValue()))
            changed |= update(CB, getSign(RI->getReturnValue()));
        }
      }
    }
    break;
  }

  default:
    break;
  }

  // nsw/nuw flags on sign-agnostic ops
  Sign fs = flagSign(I);
  if (fs != Sign::Unknown)
    changed |= update(&I, fs);

  return changed;
}

// ---------------------------------------------------------------------------
// Backward propagation: use → operands
// ---------------------------------------------------------------------------

bool SignAnalysis::propagateBackward(Instruction &I) {
  bool changed = false;

  auto constrainIntegerOperands = [&](Sign S) {
    for (auto &Op : I.operands()) {
      if (isInteger(Op.get()))
        changed |= update(Op.get(), S);
    }
  };

  switch (I.getOpcode()) {
  // Signed operations → operands are signed
  case Instruction::SDiv:
  case Instruction::SRem:
  case Instruction::AShr:
    constrainIntegerOperands(Sign::Signed);
    break;

  // Unsigned operations → operands are unsigned
  case Instruction::UDiv:
  case Instruction::URem:
  case Instruction::LShr:
    constrainIntegerOperands(Sign::Unsigned);
    break;

  // Casts constrain the source operand
  case Instruction::SExt:
    if (isInteger(I.getOperand(0)))
      changed |= update(I.getOperand(0), Sign::Signed);
    break;
  case Instruction::ZExt:
    if (isInteger(I.getOperand(0)))
      changed |= update(I.getOperand(0), Sign::Unsigned);
    break;

  // FP conversions constrain the source operand
  case Instruction::SIToFP:
    if (isInteger(I.getOperand(0)))
      changed |= update(I.getOperand(0), Sign::Signed);
    break;
  case Instruction::UIToFP:
    if (isInteger(I.getOperand(0)))
      changed |= update(I.getOperand(0), Sign::Unsigned);
    break;

  // Integer comparisons: signed/unsigned predicates constrain operands
  case Instruction::ICmp: {
    auto &Cmp = cast<ICmpInst>(I);
    if (CmpInst::isSigned(Cmp.getPredicate()))
      constrainIntegerOperands(Sign::Signed);
    else if (CmpInst::isUnsigned(Cmp.getPredicate()))
      constrainIntegerOperands(Sign::Unsigned);
    // eq/ne: no constraint
    break;
  }

  // Store: propagate stored value's sign to aliasing load results
  case Instruction::Store: {
    auto *SI = cast<StoreInst>(&I);
    auto *storedVal = SI->getValueOperand();
    if (!isInteger(storedVal))
      break;
    Sign valSign = getSign(storedVal);
    if (valSign == Sign::Unknown)
      break;
    auto cell = resolvePointer(SI->getPointerOperand());
    if (cell.first) {
      auto it = CellLoads.find(cell);
      if (it != CellLoads.end()) {
        for (auto *loadResult : it->second)
          changed |= update(loadResult, valSign);
      }
    }
    break;
  }

  // Call: propagate formal parameter signs → actual arguments
  case Instruction::Call:
  case Instruction::Invoke: {
    auto *CB = cast<CallBase>(&I);
    Function *callee = CB->getCalledFunction();
    if (!callee || callee->isDeclaration())
      break;
    for (unsigned i = 0, e = CB->arg_size(); i < e && i < callee->arg_size();
         ++i) {
      if (isInteger(CB->getArgOperand(i)))
        changed |= update(CB->getArgOperand(i), getSign(callee->getArg(i)));
    }
    break;
  }

  // Return: propagate return value sign → all CallInst results
  case Instruction::Ret: {
    auto *RI = cast<ReturnInst>(&I);
    auto *retVal = RI->getReturnValue();
    if (!retVal || !isInteger(retVal))
      break;
    Sign retSign = getSign(retVal);
    if (retSign == Sign::Unknown)
      break;
    Function *F = I.getFunction();
    for (auto *U : F->users()) {
      if (auto *CB = dyn_cast<CallBase>(U)) {
        if (CB->getCalledFunction() == F && isInteger(CB))
          changed |= update(CB, retSign);
      }
    }
    break;
  }

  default:
    break;
  }

  // nsw/nuw flags on sign-agnostic ops constrain operands too
  Sign fs = flagSign(I);
  if (fs != Sign::Unknown)
    constrainIntegerOperands(fs);

  return changed;
}

// ---------------------------------------------------------------------------
// Initialization & fixpoint
// ---------------------------------------------------------------------------

void SignAnalysis::initialize(Module &M) {
  SignMap.clear();
  for (auto &F : M) {
    for (auto &I : instructions(F)) {
      propagateForward(I);
      propagateBackward(I);
    }
  }
}

bool SignAnalysis::propagate(Module &M) {
  bool changed = false;
  for (auto &F : M) {
    for (auto &I : instructions(F)) {
      changed |= propagateForward(I);
      changed |= propagateBackward(I);
    }
  }
  return changed;
}

bool SignAnalysis::runOnModule(Module &M) {
  DSA = &getAnalysis<DSAWrapper>();
  buildMemoryIndex(M);
  initialize(M);

  unsigned iterations = 0;
  while (propagate(M))
    ++iterations;

  SDEBUG(errs() << "SignAnalysis: converged after " << iterations
                << " iteration(s), " << SignMap.size() << " values mapped\n");
  SDEBUG(dump());

  // Analysis pass — does not modify the module.
  return false;
}

void SignAnalysis::dump() const {
  errs() << "=== SignAnalysis results ===\n";
  for (auto &entry : SignMap) {
    if (entry.second == Sign::Unknown)
      continue;
    errs() << "  [" << signName(entry.second) << "] ";
    if (entry.first->hasName())
      errs() << entry.first->getName();
    else
      entry.first->printAsOperand(errs(), false);
    errs() << "\n";
  }
  errs() << "=== end SignAnalysis ===\n";
}

} // namespace smack
