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
// (sdiv, zext, signed comparisons, etc.), nsw/nuw flags, and inert
// !overflow.sign metadata produced from Clang's sanitizer-only overflow
// intrinsics. Memory propagation uses sea-dsa alias information to connect
// stores to loads. The analysis iterates to a fixpoint.
//

#define DEBUG_TYPE "smack-sign"
#include "smack/SignAnalysis.h"
#include "seadsa/Graph.hh"
#include "smack/DSAWrapper.h"
#include "smack/Debug.h"
#include "smack/IntegerOverflowChecker.h"
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

/// Classify overflow-sign metadata or the nsw/nuw flags on an
/// OverflowingBinaryOperator. Returns Signed or Unsigned for unambiguous
/// evidence and Unknown otherwise.
static Sign flagSign(const Instruction &I) {
  if (MDNode *N = I.getMetadata(OverflowSignMetadata)) {
    if (N->getNumOperands() == 1) {
      if (auto *S = dyn_cast<MDString>(N->getOperand(0).get())) {
        if (S->getString() == "s")
          return Sign::Signed;
        if (S->getString() == "u")
          return Sign::Unsigned;
      }
    }
  }

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
  // Never record a sign for a constant.  LLVM uniques ConstantInts per
  // LLVMContext, so `-1 : i32` is a single object shared by every use of that
  // bit pattern in the module.  A sign learned at one use would silently
  // become the sign at all of them, and signedness is a property of a *use*,
  // not of the constant: the same literal is legitimately signed in
  // `x sdiv -1` and unsigned in `x udiv 4294967295`.  Constant operands get
  // their sign from the surrounding computation instead -- see
  // getSign(Use).
  if (isa<Constant>(V))
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

Sign SignAnalysis::getSign(const Use &U) const {
  const Value *V = U.get();
  if (!isa<Constant>(V))
    return getSign(V);

  const User *Owner = U.getUser();
  const unsigned Operand = U.getOperandNo();
  const auto *I = dyn_cast<Instruction>(Owner);
  const auto *CE = dyn_cast<ConstantExpr>(Owner);
  if (!I && !CE)
    return Sign::Unknown;
  const unsigned Opcode = I ? I->getOpcode() : CE->getOpcode();

  // First honor operations whose opcode or predicate fixes how this exact
  // operand is interpreted.
  switch (Opcode) {
  case Instruction::SDiv:
  case Instruction::SRem:
    return Sign::Signed;
  case Instruction::UDiv:
  case Instruction::URem:
    return Sign::Unsigned;
  case Instruction::AShr:
    return Operand == 0 ? Sign::Signed : Sign::Unsigned;
  case Instruction::LShr:
    return Sign::Unsigned;
  case Instruction::Shl:
    if (Operand == 1)
      return Sign::Unsigned;
    break;
  case Instruction::SExt:
  case Instruction::SIToFP:
    return Sign::Signed;
  case Instruction::ZExt:
  case Instruction::UIToFP:
    return Sign::Unsigned;
  case Instruction::GetElementPtr:
    if (Operand > 0)
      return Sign::Signed;
    break;
  default:
    break;
  }

  if (Opcode == Instruction::ICmp) {
    CmpInst::Predicate Predicate;
    if (const auto *Cmp = dyn_cast<ICmpInst>(I))
      Predicate = Cmp->getPredicate();
    else
      Predicate = static_cast<CmpInst::Predicate>(CE->getPredicate());

    if (CmpInst::isSigned(Predicate))
      return Sign::Signed;
    if (CmpInst::isUnsigned(Predicate))
      return Sign::Unsigned;

    // Equality compares bit patterns and supplies no sign information.  In
    // particular, borrowing the other operand's inferred sign can turn a
    // signed sentinel such as -2 into 4294967294 when the value being compared
    // crossed a function boundary from unsigned storage.  Keep the established
    // signed literal fallback for eq/ne instead.
    return Sign::Unknown;
  }

  if (I) {
    Sign S = flagSign(*I);
    if (S == Sign::Signed || S == Sign::Unsigned)
      return S;
  }

  auto meetValue = [this](Sign S, const Value *Other) {
    if (!isInteger(Other) || isa<Constant>(Other))
      return S;
    return meetSign(S, getSign(Other));
  };

  // For sign-polymorphic operations, the result and only the semantically
  // related operands provide context.  In particular, this avoids treating a
  // select condition or an unrelated call argument as evidence.
  switch (Opcode) {
  case Instruction::Add:
  case Instruction::Sub:
  case Instruction::Mul:
  case Instruction::And:
  case Instruction::Or:
  case Instruction::Xor: {
    Sign S = getSign(Owner);
    for (unsigned Index = 0; Index < Owner->getNumOperands(); ++Index)
      if (Index != Operand)
        S = meetValue(S, Owner->getOperand(Index));
    return S;
  }
  case Instruction::Shl:
    return getSign(Owner);
  case Instruction::Trunc:
    return getSign(Owner);
  case Instruction::Select: {
    if (Operand == 0)
      return Sign::Unsigned;
    Sign S = getSign(Owner);
    return meetValue(S, Owner->getOperand(Operand == 1 ? 2 : 1));
  }
  case Instruction::PHI: {
    Sign S = getSign(Owner);
    for (unsigned Index = 0; Index < Owner->getNumOperands(); ++Index)
      if (Index != Operand)
        S = meetValue(S, Owner->getOperand(Index));
    return S;
  }
  case Instruction::Call:
  case Instruction::Invoke: {
    const auto *CB = cast<CallBase>(Owner);
    if (!CB->isArgOperand(&U))
      return Sign::Unknown;
    const Function *Callee = CB->getCalledFunction();
    const unsigned Arg = CB->getArgOperandNo(&U);
    if (!Callee || Arg >= Callee->arg_size())
      return Sign::Unknown;
    return getSign(Callee->getArg(Arg));
  }
  case Instruction::Ret: {
    Sign S = Sign::Unknown;
    const Function *F = cast<Instruction>(Owner)->getFunction();
    for (const User *FunctionUser : F->users())
      if (const auto *CB = dyn_cast<CallBase>(FunctionUser))
        if (CB->getCalledFunction() == F && isInteger(CB))
          S = meetSign(S, getSign(CB));
    return S;
  }
  case Instruction::Store: {
    if (Operand != 0)
      return Sign::Unknown;
    const auto *SI = cast<StoreInst>(Owner);
    auto Cell = resolvePointer(SI->getPointerOperand());
    if (!Cell.first)
      return Sign::Unknown;
    auto It = CellLoads.find(Cell);
    if (It == CellLoads.end())
      return Sign::Unknown;
    Sign S = Sign::Unknown;
    for (const Value *Load : It->second)
      S = meetSign(S, getSign(Load));
    return S;
  }
  case Instruction::Switch:
    if (Operand >= 2 && Operand % 2 == 0)
      return getSign(Owner->getOperand(0));
    return Sign::Unknown;
  default:
    return Sign::Unknown;
  }
}

// ---------------------------------------------------------------------------
// Memory index (DSA-based)
// ---------------------------------------------------------------------------

SignAnalysis::MemCell SignAnalysis::resolvePointer(const Value *Ptr) const {
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

  // GEP indices are signed (negative index = pointer decrement)
  case Instruction::GetElementPtr: {
    auto &GEP = cast<GetElementPtrInst>(I);
    for (auto idx = GEP.idx_begin(); idx != GEP.idx_end(); ++idx) {
      if (isInteger(*idx))
        changed |= update(*idx, Sign::Signed);
    }
    break;
  }

  // Sign-agnostic arithmetic: propagate result sign to operands
  case Instruction::Add:
  case Instruction::Sub:
  case Instruction::Mul: {
    Sign resultSign = getSign(&I);
    if (resultSign != Sign::Unknown)
      constrainIntegerOperands(resultSign);
    break;
  }

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
