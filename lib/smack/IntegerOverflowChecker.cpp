//
// This file is distributed under the MIT License. See LICENSE for details.
//

//
// This pass converts LLVM's checked integer-arithmetic operations into basic
// operations, and optionally allows for the checking of overflow.
//

#include "smack/IntegerOverflowChecker.h"
#include "smack/Debug.h"
#include "smack/Naming.h"
#include "smack/SmackOptions.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ValueHandle.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/Support/Regex.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"
#include <string>

#define DEBUG_TYPE "smack-overflow"

namespace smack {

using namespace llvm;

const char OverflowSignMetadata[] = "overflow.sign";

Regex OVERFLOW_INTRINSICS("^llvm.(u|s)(add|sub|mul).with.overflow.i([0-9]+)$");

static bool isSanitizerHandler(StringRef Name) {
  return Name.find("__ubsan_handle_shift_out_of_bounds") != StringRef::npos ||
         Name.find("__ubsan_handle_divrem_overflow") != StringRef::npos ||
         Name == "llvm.ubsantrap";
}

static void setOverflowSign(Instruction *I, bool isSigned) {
  LLVMContext &C = I->getContext();
  I->setMetadata(OverflowSignMetadata,
                 MDNode::get(C, MDString::get(C, isSigned ? "s" : "u")));
}

/// Clang tags every instruction of its sanitizer instrumentation (the checked
/// intrinsic, the extractvalues, the i1 logic, the branch and the handler
/// block) with !nosanitize. The annotation-only cleanup below relies on that
/// tag to distinguish the scaffolding from the program it instruments.
static bool isSanitizerScaffolding(const Instruction *I) {
  return I->getMetadata("nosanitize") != nullptr;
}

/*
 * Fold the sanitizer scaffolding reachable from Roots after its overflow flag
 * has been replaced by a constant: the i1 logic that feeds the sanitizer
 * branch is constant-folded and the branch is made unconditional, which
 * unlinks the handler block. Nothing outside the scaffolding is simplified.
 * In particular the instrumented arithmetic itself and the casts around it
 * are left as instructions; folding e.g. inttoptr(add(ptrtoint @g, k)) into a
 * ConstantExpr would change the region partition of the pointer analysis and
 * with it the memory model of the translated program.
 */
static void
foldSanitizerScaffolding(ArrayRef<WeakTrackingVH> Roots, const DataLayout &DL,
                         SmallPtrSetImpl<BasicBlock *> &Folded,
                         SmallVectorImpl<WeakTrackingVH> &Unlinked) {
  // A root may already have been erased by an earlier step; the tracking
  // handle then reads as null.
  SmallSetVector<Instruction *, 16> Worklist;
  for (const WeakTrackingVH &Root : Roots)
    if (auto *I = dyn_cast_or_null<Instruction>(static_cast<Value *>(Root)))
      Worklist.insert(I);
  while (!Worklist.empty()) {
    Instruction *I = Worklist.pop_back_val();
    if (!isSanitizerScaffolding(I))
      continue;
    if (auto *Branch = dyn_cast<BranchInst>(I)) {
      if (Branch->isConditional() && isa<ConstantInt>(Branch->getCondition())) {
        BasicBlock *BB = Branch->getParent();
        for (BasicBlock *Succ : successors(BB))
          Unlinked.push_back(Succ);
        if (ConstantFoldTerminator(BB, true))
          Folded.insert(BB);
      }
      continue;
    }
    if (I->isTerminator())
      continue;
    Constant *C = ConstantFoldInstruction(I, DL);
    if (!C)
      continue;
    for (User *U : I->users())
      if (auto *UI = dyn_cast<Instruction>(U))
        Worklist.insert(UI);
    I->replaceAllUsesWith(C);
    I->eraseFromParent();
  }
}

/*
 * Erase the sanitizer scaffolding that a folded branch left dead, such as the
 * icmp/or chain of a division check. Only !nosanitize instructions are
 * removed; a program value that becomes dead is left to the ordinary
 * dead-code elimination later in the pipeline.
 */
static void eraseDeadSanitizerScaffolding(ArrayRef<WeakTrackingVH> Roots) {
  SmallSetVector<Instruction *, 16> Worklist;
  for (const WeakTrackingVH &Root : Roots)
    if (auto *I = dyn_cast_or_null<Instruction>(static_cast<Value *>(Root)))
      Worklist.insert(I);
  while (!Worklist.empty()) {
    Instruction *I = Worklist.pop_back_val();
    if (!isSanitizerScaffolding(I) || !isInstructionTriviallyDead(I))
      continue;
    SmallVector<Instruction *, 4> Operands;
    for (Use &Op : I->operands())
      if (auto *OI = dyn_cast<Instruction>(Op))
        Operands.push_back(OI);
    I->eraseFromParent();
    for (Instruction *OI : Operands)
      Worklist.insert(OI);
  }
}

/*
 * Delete the handler blocks that folding the sanitizer branches left without
 * predecessors, and transitively whatever was reachable only through them.
 * This is deliberately narrower than removeUnreachableBlocks, whose liveness
 * scan also constant-folds every reachable terminator and rewrites code after
 * noreturn calls or stores to null; those changes are unrelated to the
 * instrumentation and would make the translation differ from an
 * uninstrumented compilation.
 */
static void eraseUnlinkedBlocks(ArrayRef<WeakTrackingVH> Candidates) {
  SmallSetVector<BasicBlock *, 8> Worklist;
  for (const WeakTrackingVH &H : Candidates)
    if (auto *BB = dyn_cast_or_null<BasicBlock>(static_cast<Value *>(H)))
      Worklist.insert(BB);
  while (!Worklist.empty()) {
    BasicBlock *BB = Worklist.pop_back_val();
    if (BB == &BB->getParent()->getEntryBlock() || !pred_empty(BB))
      continue;
    SmallVector<BasicBlock *, 2> Successors(successors(BB));
    DeleteDeadBlock(BB);
    for (BasicBlock *Succ : Successors)
      Worklist.insert(Succ);
  }
}

const std::map<std::string, Instruction::BinaryOps>
    IntegerOverflowChecker::INSTRUCTION_TABLE{{"add", Instruction::Add},
                                              {"sub", Instruction::Sub},
                                              {"mul", Instruction::Mul}};

APInt IntegerOverflowChecker::getMax(unsigned bits, bool isSigned) {
  return isSigned ? APInt::getSignedMaxValue(bits).sext(bits * 2)
                  : APInt::getMaxValue(bits).zext(bits * 2);
}

APInt IntegerOverflowChecker::getMin(unsigned bits, bool isSigned) {
  return isSigned ? APInt::getSignedMinValue(bits).sext(bits * 2)
                  : APInt::getMinValue(bits).zext(bits * 2);
}

/*
 * Optionally generates a double wide version of v for the purpose of detecting
 * overflow.
 */
Value *IntegerOverflowChecker::extendBitWidth(Value *v, int bits, bool isSigned,
                                              Instruction *i) {
  if (isSigned)
    return CastInst::CreateSExtOrBitCast(
        v, IntegerType::get(i->getFunction()->getContext(), bits * 2), "", i);
  else
    return CastInst::CreateZExtOrBitCast(
        v, IntegerType::get(i->getFunction()->getContext(), bits * 2), "", i);
}

/*
 * Generates instructions to determine whether a Value v is is out of range for
 * its bit width and sign.
 */
BinaryOperator *IntegerOverflowChecker::createFlag(Value *v, int bits,
                                                   bool isSigned,
                                                   Instruction *i) {
  auto *max = ConstantInt::get(
      IntegerType::get(i->getFunction()->getContext(), bits * 2),
      getMax(bits, isSigned));
  auto *min = ConstantInt::get(
      IntegerType::get(i->getFunction()->getContext(), bits * 2),
      getMin(bits, isSigned));
  CmpInst::Predicate maxCmpPred =
      (isSigned ? CmpInst::ICMP_SGT : CmpInst::ICMP_UGT);
  CmpInst::Predicate minCmpPred =
      (isSigned ? CmpInst::ICMP_SLT : CmpInst::ICMP_ULT);
  ICmpInst *gt = new ICmpInst(i, maxCmpPred, v, max, "");
  ICmpInst *lt = new ICmpInst(i, minCmpPred, v, min, "");
  return BinaryOperator::Create(Instruction::Or, gt, lt, "", i);
}

/*
 * Create an instruction to cast v to bits size.
 */
Value *IntegerOverflowChecker::createResult(Value *v, int bits,
                                            Instruction *i) {
  return CastInst::CreateTruncOrBitCast(
      v, IntegerType::get(i->getFunction()->getContext(), bits), "", i);
}

/*
 * This adds a call instruction to __SMACK_check_overflow to determine if an
 * overflow occured as indicated by flag.
 */
void IntegerOverflowChecker::addCheck(Function *co, Value *flag,
                                      Instruction *i) {
  Value *args = CastInst::CreateIntegerCast(flag, co->arg_begin()->getType(),
                                            false, "", i);
  CallInst::Create(co, args, "", i);
}

/*
 * This inserts a call to assume with flag negated to prevent the verifier
 * from exploring paths past a __SMACK_check_overflow
 */
void IntegerOverflowChecker::addBlockingAssume(Function *va, Value *flag,
                                               Instruction *i) {
  Value *args =
      CastInst::CreateIntegerCast(BinaryOperator::CreateNot(flag, "", i),
                                  va->arg_begin()->getType(), false, "", i);
  CallInst::Create(va, args, "", i);
}

bool IntegerOverflowChecker::runOnModule(Module &m) {
  Function *co = m.getFunction("__SMACK_check_overflow");
  assert(co != NULL && "Function __SMACK_check_overflow should be present.");
  Function *va = m.getFunction("__VERIFIER_assume");
  assert(va != NULL && "Function __VERIFIER_assume should be present.");
  // Tracking handles: a trap block reached from an intrinsic's overflow
  // branch is seen by both cleanup steps below, and whichever runs first
  // erases the shared i1 logic.
  SmallVector<WeakTrackingVH, 8> scaffoldingRoots;
  SmallVector<WeakTrackingVH, 8> deadScaffolding;
  SmallPtrSet<BasicBlock *, 8> foldedBlocks;
  SmallPtrSet<BasicBlock *, 8> handlerBlocksToRemove;
  SmallVector<WeakTrackingVH, 8> unlinkedBlocks;
  SmallVector<WeakTrackingVH, 8> blocksToMerge;
  std::vector<Instruction *> instToErase;
  bool modified = false;
  for (auto &F : m) {
    if (Naming::isSmackName(F.getName()))
      continue;
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
      if (auto ci = dyn_cast<CallInst>(&*I)) {
        Function *f = ci->getCalledFunction();
        if (f && f->hasName()) {
          auto fn = f->getName();
          // Outside the opt-in analysis, preserve the historical treatment of
          // checked-arithmetic intrinsics exactly. In particular, a user may
          // have supplied sanitizer instrumentation through --clang-options;
          // that did not previously make the intrinsic annotation-only.
          bool sanitizerInstrumentation =
              SmackOptions::SignAnalysisEnabled &&
              ci->getMetadata("nosanitize") != nullptr;
          SmallVector<StringRef, 4> frontendInfo;
          bool overflowIntrinsic = OVERFLOW_INTRINSICS.match(fn, &frontendInfo);
          if (FrontendInstrumentationOnly) {
            if (!sanitizerInstrumentation)
              continue;

            if (isSanitizerHandler(fn)) {
              // Clang emits signed division and shift checks directly as a
              // branch to a handler (or llvm.ubsantrap), without an overflow
              // intrinsic. In annotation-only mode, fold every predecessor
              // away from that handler block.
              if (!SmackOptions::IntegerOverflow) {
                handlerBlocksToRemove.insert(ci->getParent());
                modified = true;
              }
              continue;
            }

            if (!overflowIntrinsic)
              continue;

            // Preserve signed sanitizer instrumentation for the late pass when
            // the user explicitly requested overflow checking.
            if (SmackOptions::IntegerOverflow && frontendInfo[1] == "s")
              continue;
          }
          if (isSanitizerHandler(fn) && fn != "llvm.ubsantrap") {
            // If the call to __ubsan_handle_* is reachable,
            // then an overflow is possible.
            if (SmackOptions::IntegerOverflow) {
              // Add check for UBSan left shift/signed division when needed
              ConstantInt *flag =
                  ConstantInt::getTrue(ci->getFunction()->getContext());
              if (SmackOptions::shouldCheckFunction(F.getName()))
                addCheck(co, flag, ci);
              addBlockingAssume(va, flag, ci);
              ci->replaceAllUsesWith(flag);
              instToErase.push_back(ci);
              modified = true;
            }
          }
          SmallVector<StringRef, 4> info;
          if (overflowIntrinsic && OVERFLOW_INTRINSICS.match(fn, &info)) {
            /*
             * If ei is an ExtractValueInst whose value flows from an LLVM
             * checked value intrinsic f, then we do the following:
             * - The intrinsic is replaced with the non-intrinsic version of the
             *   operation.
             * - If checking is enabled, the operation is computed in double bit
             *   width.
             * - A flag is computed to determine whether an overflow occured.
             * - The overflow flag is optionally checked to raise an
             *   integer-overflow assertion violation.
             * - Finally, an assumption about the value of the flag is created
             *   to block erroneous checking of paths after the overflow check.
             */
            SDEBUG(errs() << "Processing intrinsic: " << fn << "\n");
            assert(info.size() == 4 && "Must capture three matched strings.");
            bool isSigned = (info[1] == "s");
            std::string op = info[2].str();
            unsigned bits = 0;
            auto res = info[3].getAsInteger(10, bits);
            assert(!res && "Invalid bit widths.");
            SDEBUG(errs() << "Processing operator: " << op << "\n");
            assert(INSTRUCTION_TABLE.count(op) != 0 &&
                   "Operator must be present in our instruction table.");
            bool checkThisOverflow = SmackOptions::IntegerOverflow &&
                                     (!sanitizerInstrumentation || isSigned);
            bool needsOverflowFlag =
                !sanitizerInstrumentation || checkThisOverflow;
            Value *r;
            BinaryOperator *flag = nullptr;
            if (needsOverflowFlag) {
              Value *eo1 =
                  extendBitWidth(ci->getArgOperand(0), bits, isSigned, ci);
              Value *eo2 =
                  extendBitWidth(ci->getArgOperand(1), bits, isSigned, ci);
              BinaryOperator *ai = BinaryOperator::Create(
                  INSTRUCTION_TABLE.at(op), eo1, eo2, "", ci);
              r = createResult(ai, bits, &*I);
              flag = createFlag(ai, bits, isSigned, ci);
            } else {
              auto *ai = BinaryOperator::Create(INSTRUCTION_TABLE.at(op),
                                                ci->getArgOperand(0),
                                                ci->getArgOperand(1), "", ci);
              ai->setDebugLoc(ci->getDebugLoc());
              r = ai;
            }
            if (SmackOptions::SignAnalysisEnabled)
              setOverflowSign(cast<Instruction>(r), isSigned);
            if (checkThisOverflow &&
                SmackOptions::shouldCheckFunction(F.getName()))
              addCheck(co, flag, ci);
            SmallVector<User *, 4> intrinsicUsers(ci->user_begin(),
                                                  ci->user_end());
            for (auto U : intrinsicUsers) {
              if (ExtractValueInst *ei = dyn_cast<ExtractValueInst>(U)) {
                if (ei->getNumIndices() == 1) {
                  if (ei->getIndices()[0] == 0)
                    // value part
                    ei->replaceAllUsesWith(r);
                  else if (ei->getIndices()[0] == 1) {
                    // flag part
                    // addBlockingAssume(va, flag, ei);
                    if (sanitizerInstrumentation) {
                      // The scaffolding that consumes the flag (typically
                      // `xor i1 %flag, true` and the branch to the handler)
                      // becomes constant; fold exactly that once the
                      // intrinsic is gone.
                      for (User *FlagUser : ei->users())
                        if (auto *FI = dyn_cast<Instruction>(FlagUser))
                          scaffoldingRoots.push_back(FI);
                      auto *noOverflow =
                          ConstantInt::getFalse(ei->getContext());
                      ei->replaceAllUsesWith(noOverflow);
                    } else {
                      ei->replaceAllUsesWith(flag);
                    }
                  } else
                    llvm_unreachable("Unexpected extractvalue inst!");
                  instToErase.push_back(ei);
                }
              }
            }
            instToErase.push_back(ci);
            modified = true;
          }
        }
      }
    }
  }
  for (auto I : instToErase) {
    I->eraseFromParent();
  }
  for (BasicBlock *Handler : handlerBlocksToRemove) {
    SmallVector<BasicBlock *, 2> predecessorsToFold;
    for (BasicBlock *Pred : predecessors(Handler))
      predecessorsToFold.push_back(Pred);

    for (BasicBlock *Pred : predecessorsToFold) {
      auto *Branch = dyn_cast<BranchInst>(Pred->getTerminator());
      if (!Branch || !Branch->isConditional())
        continue;

      bool HandlerOnTrue = Branch->getSuccessor(0) == Handler;
      bool HandlerOnFalse = Branch->getSuccessor(1) == Handler;
      if (HandlerOnTrue == HandlerOnFalse)
        continue;

      // The old condition is the check's icmp/or chain; it is dead once the
      // branch no longer reads it.
      deadScaffolding.push_back(Branch->getCondition());
      Branch->setCondition(HandlerOnTrue
                               ? ConstantInt::getFalse(Branch->getContext())
                               : ConstantInt::getTrue(Branch->getContext()));
      if (ConstantFoldTerminator(Pred, true))
        foldedBlocks.insert(Pred);
    }
    unlinkedBlocks.push_back(Handler);
  }
  foldSanitizerScaffolding(scaffoldingRoots, m.getDataLayout(), foldedBlocks,
                           unlinkedBlocks);
  eraseDeadSanitizerScaffolding(deadScaffolding);
  for (BasicBlock *BB : foldedBlocks)
    if (BasicBlock *Succ = BB->getSingleSuccessor())
      blocksToMerge.push_back(Succ);
  eraseUnlinkedBlocks(unlinkedBlocks);
  // Re-join the block Clang split off after each check so that the CFG
  // matches the uninstrumented compilation; no instruction is simplified.
  for (WeakTrackingVH &Handle : blocksToMerge) {
    Value *V = Handle;
    if (auto *BB = dyn_cast_or_null<BasicBlock>(V))
      MergeBlockIntoPredecessor(BB);
  }

  // The legacy pass reported the module as modified unconditionally. Keep
  // that pass-manager behavior when the optional analysis is disabled.
  return SmackOptions::SignAnalysisEnabled ? modified : true;
}

// Pass ID variable
char IntegerOverflowChecker::ID = 0;

StringRef IntegerOverflowChecker::getPassName() const {
  return "Checked integer arithmetic intrinsics";
}
} // namespace smack
