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

Sign legacyLiteralSign(const Use &U) {
  const auto *CI = dyn_cast<ConstantInt>(U.get());
  if (!CI || CI->getBitWidth() <= 1 || !CI->isNegative())
    return Sign::Unknown;

  const User *Owner = U.getUser();
  const unsigned Operand = U.getOperandNo();
  const auto *I = dyn_cast<Instruction>(Owner);
  const auto *CE = dyn_cast<ConstantExpr>(Owner);
  if (!I && !CE)
    return Sign::Signed;

  const unsigned Opcode = I ? I->getOpcode() : CE->getOpcode();
  switch (Opcode) {
  case Instruction::SDiv:
  case Instruction::SRem:
    return Sign::Signed;
  case Instruction::UDiv:
  case Instruction::URem:
  case Instruction::Sub:
    return Sign::Unsigned;
  case Instruction::Select:
    return Operand == 0 ? Sign::Signed : Sign::Unsigned;
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
    return CmpInst::isUnsigned(Predicate) ? Sign::Unsigned : Sign::Signed;
  }

  // SMACK's original operation-local heuristic: an ordinary binary operation
  // without nsw treats the literal as unsigned, except that the common -1
  // decrement stays signed. Only add/sub/mul/shl carry wrap flags; and/or/
  // xor/lshr/ashr are not OverflowingBinaryOperators and must not be asked.
  if (const auto *BO = dyn_cast_or_null<BinaryOperator>(I)) {
    const auto *OBO = dyn_cast<OverflowingBinaryOperator>(BO);
    if (!OBO || !OBO->hasNoSignedWrap())
      return CI->isMinusOne() ? Sign::Signed : Sign::Unsigned;
  }
  return Sign::Signed;
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
  // Anything else (a global initializer, metadata) is outside the SSA graph
  // this analysis can follow: the value escapes.
  if (!I && !CE)
    return Sign::Conflict;

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

    // Equality compares bit patterns. Under the integer encoding one bit
    // pattern has two representatives (-k and 2^N - k), so a literal in an
    // eq/ne must be spelled in the window of the SSA value it meets, or the
    // comparison silently fails. That window is the value's own inferred
    // sign: its producer-side literals (phi/select/argument/return) are
    // rendered from the same inferValue result, so both sides agree by
    // construction. When the other operand is itself a constant there is no
    // value to agree with. The non-constant operand receives no window
    // information from an equality and the value cannot flow through it.
    if (isa<ConstantInt>(U.get())) {
      const Value *Other = Owner->getOperand(1 - Operand);
      if (isInteger(Other) && !isa<Constant>(Other))
        return inferValue(Other, VisitedValues);
    }
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
  //
  // Unknown is reserved for consumers that carry no window information AND
  // cannot forward the value anywhere. Every consumer this analysis cannot
  // see through (memory, calls it cannot follow, unlisted opcodes) returns
  // Conflict instead: it is not "no evidence" but "the value escapes", and
  // only a value whose entire consumer set is classified may take the
  // unsigned window. Conflict renders signed, the pre-analysis behavior.
  switch (Opcode) {
  case Instruction::Add:
  case Instruction::Sub:
  case Instruction::Mul:
  case Instruction::And:
  case Instruction::Or:
  case Instruction::Xor:
  case Instruction::Shl: {
    Sign S = inferValue(Owner, VisitedValues);
    return S == Sign::Unknown ? legacyLiteralSign(U) : S;
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
  case Instruction::Store:
    // The stored value escapes to memory; its readers are invisible here.
    return Sign::Conflict;
  case Instruction::Call:
  case Instruction::Invoke: {
    // Only an argument of a direct call to a function defined in this module
    // can be followed into the callee. Indirect calls, intrinsics, external
    // declarations and variadic arguments escape.
    const auto *CB = cast<CallBase>(Owner);
    const Function *Callee = CB->getCalledFunction();
    if (!CB->isArgOperand(&U) || !Callee || Callee->isDeclaration())
      return Sign::Conflict;
    const unsigned Arg = CB->getArgOperandNo(&U);
    if (Arg >= Callee->arg_size())
      return Sign::Conflict;
    return inferValue(Callee->getArg(Arg), VisitedValues);
  }
  case Instruction::Ret: {
    // Meet over every direct call site of the function in the module: the
    // returned value is consumed wherever the function is called, so this
    // result is non-local by design. A function whose address is taken can
    // be called from sites this walk cannot see, so the value escapes. A
    // call site that ignores the result contributes nothing.
    Sign S = Sign::Unknown;
    const Function *F = I->getFunction();
    for (const User *FunctionUser : F->users()) {
      const auto *CB = dyn_cast<CallBase>(FunctionUser);
      if (!CB || CB->getCalledFunction() != F)
        return Sign::Conflict;
      if (!isInteger(CB))
        continue;
      S = meetSign(S, inferValue(CB, VisitedValues));
      if (S == Sign::Conflict)
        break;
    }
    return S;
  }
  default:
    // Switch, inttoptr, bitcast, insertvalue, atomics, alloca sizes, ...:
    // no window information and no way to follow the value.
    return Sign::Conflict;
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
