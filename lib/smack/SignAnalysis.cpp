//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/SignAnalysis.h"
#include "smack/IntegerOverflowChecker.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/raw_ostream.h"

namespace smack {

using namespace llvm;

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

static bool isInteger(const Value *V) {
  return V && V->getType()->isIntegerTy();
}

/// Classify explicit sign information attached to an ordinary arithmetic
/// instruction. Both flags means that either interpretation is valid, so it
/// does not provide a unique sign.
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

char SignAnalysis::ID = 0;
static RegisterPass<SignAnalysis> X("smack-sign",
                                    "Integer literal use-context analysis");

StringRef SignAnalysis::getPassName() const {
  return "Integer literal use-context analysis";
}

void SignAnalysis::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
}

bool SignAnalysis::runOnModule(Module &) {
  SignCache.clear();
  return false;
}

Sign SignAnalysis::legacyLiteralFallback(const Use &U) const {
  const auto *CI = dyn_cast<ConstantInt>(U.get());
  if (!CI || CI->getBitWidth() <= 1 || !CI->isNegative())
    return Sign::Unknown;

  const auto *I = dyn_cast<Instruction>(U.getUser());
  const auto *CE = dyn_cast<ConstantExpr>(U.getUser());
  if (!I && !CE)
    return Sign::Unknown;

  unsigned Opcode = I ? I->getOpcode() : CE->getOpcode();

  // Preserve the old operation-local behavior when Clang did not provide
  // sanitizer metadata, most importantly for uninstrumented library code.
  // Trust nsw/nuw first when they are available.
  if (I) {
    if (auto *OBO = dyn_cast<OverflowingBinaryOperator>(I)) {
      if (OBO->hasNoSignedWrap())
        return Sign::Signed;
      if (OBO->hasNoUnsignedWrap())
        return Sign::Unsigned;
    }
  }

  switch (Opcode) {
  case Instruction::Sub:
    return Sign::Unsigned;
  case Instruction::Add:
  case Instruction::Mul:
  case Instruction::Shl:
  case Instruction::And:
  case Instruction::Or:
  case Instruction::Xor:
    // The historical heuristic kept -1 signed because decrement commonly
    // appears as add -1, while other high-bit patterns were printed unsigned.
    return CI->isMinusOne() ? Sign::Signed : Sign::Unsigned;
  default:
    return Sign::Unknown;
  }
}

Sign SignAnalysis::inferValue(
    const Value *V, SmallPtrSetImpl<const Value *> &VisitedValues) const {
  if (!isInteger(V) || isa<ConstantInt>(V))
    return Sign::Unknown;

  auto Cached = SignCache.find(V);
  if (Cached != SignCache.end())
    return Cached->second;

  // PHIs and recursive calls can create cycles. Each reachable value only
  // needs to be visited once: evidence from its first traversal is already
  // included in the result of this root query.
  bool CacheResult = VisitedValues.empty();
  if (!VisitedValues.insert(V).second)
    return Sign::Unknown;

  Sign S = Sign::Unknown;
  for (const Use &U : V->uses()) {
    S = meetSign(S, inferUse(U, VisitedValues));
    if (S == Sign::Conflict)
      break;
  }

  // A value reached while another value is being resolved may have seen an
  // in-progress cycle and therefore does not have a context-independent
  // result. Only cache a query that started with an empty traversal set.
  if (CacheResult)
    SignCache[V] = S;
  return S;
}

Sign SignAnalysis::inferUse(
    const Use &U, SmallPtrSetImpl<const Value *> &VisitedValues) const {
  const User *Owner = U.getUser();
  const unsigned Operand = U.getOperandNo();
  const auto *I = dyn_cast<Instruction>(Owner);
  const auto *CE = dyn_cast<ConstantExpr>(Owner);
  if (!I && !CE)
    return Sign::Unknown;

  const unsigned Opcode = I ? I->getOpcode() : CE->getOpcode();

  // Operations whose opcode fixes how this exact operand is interpreted.
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
    // The owner may be an icmp constant expression, in which case I is null.
    if (const auto *Cmp = dyn_cast_or_null<ICmpInst>(I))
      Predicate = Cmp->getPredicate();
    else
      Predicate = static_cast<CmpInst::Predicate>(CE->getPredicate());

    if (CmpInst::isSigned(Predicate))
      return Sign::Signed;
    if (CmpInst::isUnsigned(Predicate))
      return Sign::Unsigned;

    // Equality compares bit patterns and supplies no sign information. In
    // particular, do not borrow a sign from the other operand or result.
    return Sign::Unknown;
  }

  // A negative literal that is a direct operand of add/sub/mul is always
  // spelled in the signed window. Under the unbounded Int encoding $add, $sub
  // and $mul do not wrap, so x + (-k) is the only rendering that computes the
  // C decrement: x + (2^N - k) never comes back below 2^N. Consumer evidence
  // and the sanitizer "u" tag describe the window of the VALUE, not how a
  // literal must be spelled inside a non-wrapping operation, so neither is
  // consulted for this operand. (Under the bit-vector and wrapped-integer
  // encodings both spellings denote the same bit pattern, so this is safe
  // there as well.)
  if (Opcode == Instruction::Add || Opcode == Instruction::Sub ||
      Opcode == Instruction::Mul) {
    if (const auto *CI = dyn_cast<ConstantInt>(U.get()))
      if (CI->getBitWidth() > 1 && CI->isNegative())
        return Sign::Signed;
  }

  if (I) {
    Sign S = flagSign(*I);
    if (S != Sign::Unknown)
      return S;
  }

  // Sign-polymorphic operations get their interpretation from consumers of
  // their result. This follows PHI/select/trunc chains in either direction
  // without assigning a permanent sign to the intermediate SSA value.
  switch (Opcode) {
  case Instruction::Add:
  case Instruction::Sub:
  case Instruction::Mul:
  case Instruction::And:
  case Instruction::Or:
  case Instruction::Xor: {
    Sign S = inferValue(Owner, VisitedValues);
    return S == Sign::Unknown ? legacyLiteralFallback(U) : S;
  }
  case Instruction::Shl: {
    Sign S = inferValue(Owner, VisitedValues);
    return S == Sign::Unknown ? legacyLiteralFallback(U) : S;
  }
  case Instruction::Trunc:
  case Instruction::Freeze:
    return inferValue(Owner, VisitedValues);
  case Instruction::Select:
    if (Operand == 0)
      return Sign::Unsigned;
    return inferValue(Owner, VisitedValues);
  case Instruction::PHI:
    return inferValue(Owner, VisitedValues);
  case Instruction::Call:
  case Instruction::Invoke: {
    const auto *CB = cast<CallBase>(Owner);
    if (!CB->isArgOperand(&U))
      return Sign::Unknown;
    const Function *Callee = CB->getCalledFunction();
    const unsigned Arg = CB->getArgOperandNo(&U);
    if (!Callee || Arg >= Callee->arg_size())
      return Sign::Unknown;
    return inferValue(Callee->getArg(Arg), VisitedValues);
  }
  case Instruction::Ret: {
    Sign S = Sign::Unknown;
    const Function *F = I->getFunction();
    for (const User *FunctionUser : F->users()) {
      const auto *CB = dyn_cast<CallBase>(FunctionUser);
      if (!CB || CB->getCalledFunction() != F || !isInteger(CB))
        continue;
      S = meetSign(S, inferValue(CB, VisitedValues));
      if (S == Sign::Conflict)
        break;
    }
    return S;
  }
  default:
    return Sign::Unknown;
  }
}

Sign SignAnalysis::getSign(const Value *V) const {
  SmallPtrSet<const Value *, 32> VisitedValues;
  return inferValue(V, VisitedValues);
}

Sign SignAnalysis::getSign(const Use &U) const {
  SmallPtrSet<const Value *, 32> VisitedValues;
  return inferUse(U, VisitedValues);
}

void SignAnalysis::dump() const {
  errs() << "=== SignAnalysis memoized results ===\n";
  for (const auto &Entry : SignCache) {
    errs() << "  [" << signName(Entry.second) << "] ";
    if (Entry.first->hasName())
      errs() << Entry.first->getName();
    else
      Entry.first->printAsOperand(errs(), false);
    errs() << "\n";
  }
  errs() << "=== end SignAnalysis ===\n";
}

} // namespace smack
