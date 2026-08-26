//
// This file is distributed under the MIT License. See LICENSE for details.
//
#define DEBUG_TYPE "smack-inst-gen"
#include "smack/SmackInstGenerator.h"
#include "smack/BoogieAst.h"
#include "smack/Debug.h"
#include "smack/LoopBoundWarnings.h"
#include "smack/Naming.h"
#include "smack/SmackOptions.h"
#include "smack/SmackRep.h"
#include "smack/VectorOperations.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Support/GraphWriter.h"
#include <sstream>

#include "llvm/Support/raw_ostream.h"
#include <functional>
#include <iostream>

#include "smack/SmackWarnings.h"
#include "llvm/IR/IntrinsicInst.h"

namespace smack {

using llvm::errs;
using namespace llvm;

const bool SHOW_ORIG = false;

#define ORIG(ins)                                                              \
  if (SHOW_ORIG)                                                               \
  emit(Stmt::comment(i2s(ins)))

Regex VAR_DECL("^[[:space:]]*var[[:space:]]+([[:alpha:]_.$#'`~^\\?][[:alnum:]_."
               "$#'`~^\\?]*):.*;");

// Procedures whose return value should not be marked as external
Regex EXTERNAL_PROC_IGNORE("^(malloc|__VERIFIER_nondet)$");

std::string i2s(const llvm::Instruction &i) {
  std::string s;
  llvm::raw_string_ostream ss(s);
  ss << i;
  s = s.substr(2);
  return s;
}

Type *getElemType(const Type *t, unsigned idx) {
  if (const llvm::StructType *st = llvm::dyn_cast<const llvm::StructType>(t))
    return st->getElementType(idx);
  else if (const llvm::ArrayType *at = llvm::dyn_cast<const llvm::ArrayType>(t))
    return at->getElementType();
  else
    llvm_unreachable("Unexpected aggregate type.");
}

void SmackInstGenerator::emit(const Stmt *s) {
  // stringstream str;
  // s->print(str);
  // SDEBUG(llvm::errs() << "emit:   " << str.str() << "\n");
  currBlock->addStmt(s);
}

void SmackInstGenerator::generateFunction(llvm::Function &F) {
  prepareFunctionalLoops(F);
  for (auto &BB : F)
    if (!suppressedBlocks.count(&BB))
      visit(BB);
}

void SmackInstGenerator::prepareFunctionalLoops(llvm::Function &F) {
  if (!SmackOptions::FunctionalizeLoops || SmackOptions::BitPrecise ||
      SmackOptions::BitPrecisePointers ||
      SmackOptions::WrappedIntegerEncoding || SmackOptions::MemoryModelDebug) {
    // LoopBoundWarnings recorded the counts before NormalizeLoops; asking
    // ScalarEvolution again here, on the normalized loops, is what crashed
    // LLVM 14 on some large drivers.
    if (emitLoopBoundWarnings)
      warnAboutLoops(F, recordedLoopBoundInfo(loops));
    return;
  }

  std::vector<LoopBoundInfo> LoopBounds;
  if (emitLoopBoundWarnings)
    LoopBounds = recordedLoopBoundInfo(loops);

  auto Candidates = FunctionalLoopSummaryAnalysis::analyze(
      F, loops, *scalarEvolution, *aliasAnalysis, *memorySSA);
  for (auto &Summary : Candidates) {
    if (Summary.kind == FunctionalLoopSummary::Kind::ReadOnlyVerifier &&
        !SmackOptions::shouldCheckFunction(F.getName())) {
      bool HasAssertion = false;
      for (const auto &Action : Summary.verifierActions)
        HasAssertion |=
            Action.kind == FunctionalLoopVerifierAction::Kind::Assertion;
      if (HasAssertion)
        continue;
    }
    bool SupportedMemory = true;
    for (const auto &Store : Summary.stores)
      SupportedMemory &= rep->canFunctionalizeMemory(
          Store.store->getPointerOperand(),
          Store.store->getValueOperand()->getType());
    for (const auto &Load : Summary.loads)
      SupportedMemory &=
          Summary.kind != FunctionalLoopSummary::Kind::MemoryUpdate
              ? rep->canFunctionalizeRead(Load.load->getPointerOperand(),
                                          Load.load->getType())
              : rep->canFunctionalizeMemory(Load.load->getPointerOperand(),
                                            Load.load->getType());
    if (SupportedMemory)
      functionalLoops.push_back(std::move(Summary));
  }

  for (const auto &Summary : functionalLoops) {
    auto *Branch = dyn_cast<BranchInst>(Summary.preheader->getTerminator());
    if (!Branch)
      continue;
    if (Summary.kind != FunctionalLoopSummary::Kind::MemoryUpdate) {
      if (Branch->isUnconditional()) {
        if (Branch->getSuccessor(0) != Summary.loop->getHeader())
          continue;
      } else {
        bool HasHeaderSuccessor = false;
        bool HasExitSuccessor = false;
        for (BasicBlock *Successor : Branch->successors()) {
          HasHeaderSuccessor |= Successor == Summary.loop->getHeader();
          HasExitSuccessor |= Successor == Summary.exit;
        }
        if (Summary.kind != FunctionalLoopSummary::Kind::ReadOnlyVerifier ||
            !HasHeaderSuccessor || !HasExitSuccessor)
          continue;
      }
      summariesByPreheader[Branch] = &Summary;
      suppressedBlocks.insert(Summary.loop->block_begin(),
                              Summary.loop->block_end());
      continue;
    }
    if (Branch->isUnconditional()) {
      if (Branch->getSuccessor(0) != Summary.loop->getHeader())
        continue;
    } else {
      bool HasHeaderSuccessor = false;
      bool HasExitSuccessor = false;
      for (BasicBlock *Successor : Branch->successors()) {
        HasHeaderSuccessor |= Successor == Summary.loop->getHeader();
        HasExitSuccessor |= Successor == Summary.exit;
      }
      if (!HasHeaderSuccessor || !HasExitSuccessor)
        continue;
    }
    summariesByPreheader[Branch] = &Summary;
    if (Summary.inductionEscapes)
      nameInstruction(*Summary.induction);
    suppressedBlocks.insert(Summary.loop->block_begin(),
                            Summary.loop->block_end());
  }

  if (emitLoopBoundWarnings) {
    std::set<const Loop *> SummarizedLoops;
    for (const auto &Entry : summariesByPreheader)
      SummarizedLoops.insert(Entry.second->loop);
    warnAboutLoops(F, LoopBounds, SummarizedLoops);
  }
}

const Expr *SmackInstGenerator::functionalExpr(const llvm::Value *V) {
  // Constants (literals, global addresses, undef) print as literals or Boogie
  // constants and may appear in an axiom as they are; anything else is a
  // procedure local or parameter and must become an argument of the map.
  if (functionalCapture && !isa<Constant>(V))
    functionalCapture->emplace(naming->get(*V), rep->type(V->getType()));
  return rep->expr(V);
}

const Expr *SmackInstGenerator::functionalMap(const std::string &Name,
                                              const std::string &Type) {
  if (functionalCapture)
    functionalCapture->emplace(Name, Type);
  return Expr::id(Name);
}

// A summary map is the Boogie lambda `(lambda index :: body)` over the values
// captured in `capture`. It is emitted the way Boogie's own
// /freeVarLambdaLifting would emit it, as a map-valued function of the captured
// values defined by ONE read axiom whose only trigger is a read of the result:
//
//   function name(captured...) returns (type);
//   axiom (forall captured..., index :: {name(captured...)[index]}
//          name(captured...)[index] == body);
//
// A read of the summarised map is then expanded on demand into reads of the
// loop-entry maps it captured, which are proper subterms of the trigger, so an
// instance can only create reads on strictly earlier memory and the axiom
// cannot match on its own output. The Corral distribution SMACK targets
// (1.1.8, Boogie 2.9.1) rejects lambda expressions outright; this form is
// accepted by every Boogie SMACK has been used with. The axiom carries
// {:weight 0} for the same reason as SmackRep::intrinsicSummary: the depth
// of a chain of summaries must not turn into a Z3 generation cost and a
// spurious `unknown`.
const Expr *SmackInstGenerator::liftFunctionalMap(
    const std::string &Name, Binding Index, const Expr *Body,
    const std::map<std::string, std::string> &Capture, const std::string &Type,
    const std::string &Qid) {
  std::list<Binding> Params(Capture.begin(), Capture.end());
  std::list<const Expr *> Args;
  for (const auto &P : Params)
    Args.push_back(Expr::id(P.first));
  const Expr *Map = Expr::fn(Name, Args);
  const Expr *Read = Expr::sel(Map, Expr::id(Index.first));
  std::list<Binding> Bound = Params;
  Bound.push_back(Index);
  auto &Decls = rep->getProgram()->getDeclarations();
  Decls.push_back(Decl::function(Name, Params, Type));
  Decls.push_back(Decl::axiom(
      Expr::forall(Bound, {Attr::attr("qid", Qid), Attr::attr("weight", 0)},
                   Read, Expr::eq(Read, Body))));
  return Map;
}

const Expr *SmackInstGenerator::functionalIntegerSCEV(const SCEV *S) {
  if (auto *Constant = dyn_cast<SCEVConstant>(S))
    return rep->expr(Constant->getValue());
  if (auto *Unknown = dyn_cast<SCEVUnknown>(S))
    return functionalExpr(Unknown->getValue());
  if (auto *NAry = dyn_cast<SCEVNAryExpr>(S)) {
    std::string Operation;
    if (isa<SCEVAddExpr>(NAry))
      Operation = "$add";
    else if (isa<SCEVMulExpr>(NAry))
      Operation = "$mul";
    else
      llvm_unreachable("unsupported n-ary functional SCEV");
    auto Name = rep->opName(Operation, std::list<const Type *>{S->getType()});
    auto It = NAry->op_begin();
    const Expr *Result = functionalIntegerSCEV(*It++);
    for (; It != NAry->op_end(); ++It)
      Result = Expr::fn(Name, Result, functionalIntegerSCEV(*It));
    return Result;
  }
  if (auto *Div = dyn_cast<SCEVUDivExpr>(S)) {
    auto Name = rep->opName("$udiv", std::list<const Type *>{S->getType()});
    return Expr::fn(Name, functionalIntegerSCEV(Div->getLHS()),
                    functionalIntegerSCEV(Div->getRHS()));
  }
  if (auto *Cast = dyn_cast<SCEVCastExpr>(S)) {
    std::string Operation;
    if (isa<SCEVTruncateExpr>(Cast))
      Operation = "$trunc";
    else if (isa<SCEVZeroExtendExpr>(Cast))
      Operation = "$zext";
    else if (isa<SCEVSignExtendExpr>(Cast))
      Operation = "$sext";
    else
      llvm_unreachable("unsupported functional SCEV cast");
    auto Name = rep->opName(
        Operation,
        std::list<const Type *>{Cast->getOperand()->getType(), S->getType()});
    return Expr::fn(Name, functionalIntegerSCEV(Cast->getOperand()));
  }
  llvm_unreachable("unsupported functional integer SCEV");
}

const Expr *SmackInstGenerator::functionalPointerSCEV(const SCEV *S) {
  const SCEV *BaseSCEV = scalarEvolution->getPointerBase(S);
  auto *Base = dyn_cast<SCEVUnknown>(BaseSCEV);
  assert(Base && "validated affine pointer must have an unknown base");
  const Expr *Result = functionalExpr(Base->getValue());
  const SCEV *Offset = scalarEvolution->removePointerBase(S);
  if (auto *Constant = dyn_cast<SCEVConstant>(Offset))
    if (Constant->getAPInt().isZero())
      return Result;

  auto *OffsetType = cast<IntegerType>(Offset->getType());
  auto OffsetAsPointer =
      Expr::fn(indexedName("$i2p", {rep->type(OffsetType), Naming::PTR_TYPE}),
               functionalIntegerSCEV(Offset));
  return Expr::fn("$add.ref", Result, OffsetAsPointer);
}

const Expr *SmackInstGenerator::functionalInductionValue(
    const FunctionalLoopSummary &Summary, const Expr *Iteration) {
  auto *Start = dyn_cast<ConstantInt>(Summary.inductionStart);
  if (Start && Start->isZero() && Summary.inductionStep->isOne())
    return Iteration;

  auto MulName = rep->opName("$mul", {Summary.iterationType});
  auto AddName = rep->opName("$add", {Summary.iterationType});
  auto Scaled = Expr::fn(MulName, rep->expr(Summary.inductionStep), Iteration);
  return Expr::fn(AddName, functionalExpr(Summary.inductionStart), Scaled);
}

const Expr *
SmackInstGenerator::functionalAddress(const AffineLoopAccess &Access,
                                      const Expr *Iteration,
                                      const IntegerType *IterationTy) {
  std::string IterationType = rep->type(IterationTy);
  auto IterationAsPointer = Expr::fn(
      indexedName("$i2p", {IterationType, Naming::PTR_TYPE}), Iteration);
  auto Offset =
      Expr::fn("$mul.ref", IterationAsPointer,
               rep->pointerLit(static_cast<unsigned long long>(Access.stride)));
  const Expr *Start = functionalPointerSCEV(Access.start);
  return Expr::fn("$add.ref", Start, Offset);
}

const Expr *SmackInstGenerator::functionalValue(
    const Value *Value, const FunctionalLoopSummary &Summary,
    const Expr *Iteration,
    const std::map<std::string, std::string> &EntryMemories) {
  if (Value == Summary.induction)
    return functionalInductionValue(Summary, Iteration);
  if (isa<Constant>(Value) || Summary.loop->isLoopInvariant(Value))
    return functionalExpr(Value);

  for (const auto &Recurrence : Summary.recurrences) {
    if (Recurrence.value != Value)
      continue;
    // start +/- step*k, with the step literal rendered exactly as
    // SmackRep::bop renders the update's constant operand (the sign
    // convention differs between `add` without nsw and `sub`), so the closed
    // form is the value the unrolled loop computes.
    bool Sub = Recurrence.update->getOpcode() == Instruction::Sub;
    auto MulName = rep->opName("$mul", {Summary.iterationType});
    auto OpName = rep->opName(Sub ? "$sub" : "$add", {Summary.iterationType});
    const Expr *Step = rep->expr(
        Recurrence.step, Sub || !Recurrence.update->hasNoSignedWrap(), Sub);
    return Expr::fn(OpName, functionalExpr(Recurrence.start),
                    Expr::fn(MulName, Step, Iteration));
  }

  if (auto *Load = dyn_cast<LoadInst>(Value)) {
    const AffineLoopAccess *Access = nullptr;
    for (const auto &Candidate : Summary.loads)
      if (Candidate.load == Load)
        Access = &Candidate.access;
    assert(Access && "validated functional load must have an affine access");
    auto Path = rep->memPath(Load->getPointerOperand());
    return rep->functionalLoad(
        Load->getPointerOperand(),
        functionalMap(EntryMemories.at(Path),
                      rep->memType(Load->getPointerOperand())),
        functionalAddress(*Access, Iteration, Summary.iterationType));
  }

  if (auto *BO = dyn_cast<BinaryOperator>(Value)) {
    // Constant operands take the representative SmackRep::bop would give them
    // for this opcode; under the unbounded encoding the two representatives
    // of a bit pattern are different integers.
    unsigned Opcode = BO->getOpcode();
    bool IsUnsigned = !BO->hasNoSignedWrap();
    bool IsUnsignedInst = false;
    if (Opcode == Instruction::SDiv || Opcode == Instruction::SRem) {
      IsUnsigned = false;
    } else if (Opcode == Instruction::UDiv || Opcode == Instruction::URem ||
               Opcode == Instruction::Sub) {
      IsUnsigned = true;
      IsUnsignedInst = true;
    }
    auto Operand = [&](const llvm::Value *V) {
      if (isa<ConstantInt>(V))
        return rep->expr(V, IsUnsigned, IsUnsignedInst);
      return functionalValue(V, Summary, Iteration, EntryMemories);
    };
    auto Name = rep->opName(Naming::INSTRUCTION_TABLE.at(Opcode),
                            std::list<const Type *>{BO->getType()});
    return Expr::fn(Name, Operand(BO->getOperand(0)),
                    Operand(BO->getOperand(1)));
  }

  if (auto *Cast = dyn_cast<CastInst>(Value)) {
    auto Name =
        rep->opName(Naming::INSTRUCTION_TABLE.at(Cast->getOpcode()),
                    std::list<const Type *>{Cast->getOperand(0)->getType(),
                                            Cast->getType()});
    return Expr::fn(Name, functionalValue(Cast->getOperand(0), Summary,
                                          Iteration, EntryMemories));
  }

  if (auto *Cmp = dyn_cast<ICmpInst>(Value)) {
    auto Operand = [&](const llvm::Value *V) {
      if (isa<ConstantInt>(V))
        return rep->expr(V, Cmp->isUnsigned(), true);
      return functionalValue(V, Summary, Iteration, EntryMemories);
    };
    auto Name = rep->opName(Naming::CMPINST_TABLE.at(Cmp->getPredicate()),
                            {Cmp->getOperand(0)->getType()});
    return Expr::fn(Name, Operand(Cmp->getOperand(0)),
                    Operand(Cmp->getOperand(1)));
  }

  if (auto *Select = dyn_cast<SelectInst>(Value)) {
    auto Condition = functionalValue(Select->getCondition(), Summary, Iteration,
                                     EntryMemories);
    // SmackRep::select renders constant arms as unsigned magnitudes.
    auto Arm = [&](const llvm::Value *V) {
      if (isa<ConstantInt>(V))
        return rep->expr(V, true, true);
      return functionalValue(V, Summary, Iteration, EntryMemories);
    };
    return Expr::ifThenElse(Expr::eq(Condition, rep->integerLit(1ULL, 1)),
                            Arm(Select->getTrueValue()),
                            Arm(Select->getFalseValue()));
  }

  llvm_unreachable("unsupported value in validated functional loop summary");
}

void SmackInstGenerator::emitReadOnlyFunctionalLoop(
    const FunctionalLoopSummary &Summary, BranchInst &PreheaderBranch) {
  unsigned Id = functionalLoopId++;
  std::string IterationType = rep->type(Summary.iterationType);
  const Expr *Zero =
      rep->integerLit(0ULL, Summary.iterationType->getBitWidth());
  const Expr *IterationCount = functionalIntegerSCEV(Summary.iterationCount);

  std::map<std::string, std::string> CurrentMemories;
  for (const auto &Load : Summary.loads) {
    std::string Path = rep->memPath(Load.load->getPointerOperand());
    CurrentMemories[Path] = Path;
  }

  auto PredicateAt = [&](const Value *PredicateValue, bool PredicateIsNonzero,
                         bool ContinueConditionValue, const Expr *Iteration) {
    const Expr *Condition =
        functionalValue(PredicateValue, Summary, Iteration, CurrentMemories);
    if (PredicateIsNonzero) {
      auto *ConditionType = cast<IntegerType>(PredicateValue->getType());
      return Expr::neq(
          Condition,
          rep->integerLit(0ULL, ConditionType->getIntegerBitWidth()));
    }
    const Expr *ConditionIsTrue = Expr::eq(Condition, rep->integerLit(1ULL, 1));
    return ContinueConditionValue ? ConditionIsTrue
                                  : Expr::not_(ConditionIsTrue);
  };
  auto ActionAt = [&](const FunctionalLoopVerifierAction &Action,
                      const Expr *Iteration) {
    return PredicateAt(Action.predicateValue, Action.predicateIsNonzero,
                       Action.continueConditionValue, Iteration);
  };
  auto AllActionsAt = [&](const Expr *Iteration) {
    const Expr *Result = Expr::lit(true);
    for (const auto &Action : Summary.verifierActions)
      Result = Expr::and_(Result, ActionAt(Action, Iteration));
    return Result;
  };
  bool IsVerifier =
      Summary.kind == FunctionalLoopSummary::Kind::ReadOnlyVerifier;
  bool HasAssertion = false;
  bool HasAssumption = false;
  for (const auto &Action : Summary.verifierActions) {
    HasAssertion |=
        Action.kind == FunctionalLoopVerifierAction::Kind::Assertion;
    HasAssumption |=
        Action.kind == FunctionalLoopVerifierAction::Kind::Assumption;
  }
  auto AssumptionsAt = [&](const Expr *Iteration) {
    const Expr *Result = Expr::lit(true);
    for (const auto &Action : Summary.verifierActions)
      if (Action.kind == FunctionalLoopVerifierAction::Kind::Assumption)
        Result = Expr::and_(Result, ActionAt(Action, Iteration));
    return Result;
  };
  auto ContinueAt = [&](const Expr *Iteration) {
    return IsVerifier ? AllActionsAt(Iteration)
                      : PredicateAt(Summary.predicateValue, false,
                                    Summary.continueConditionValue, Iteration);
  };
  auto IterationInDomain = [&](const Expr *Iteration) {
    return Expr::and_(
        Expr::fn(indexedName("$uge", {IterationType, Naming::BOOL_TYPE}),
                 Iteration, Zero),
        Expr::fn(indexedName("$ult", {IterationType, Naming::BOOL_TYPE}),
                 Iteration, IterationCount));
  };

  const Expr *FirstStop = nullptr;
  if ((!IsVerifier || HasAssumption) && !Summary.accessChecks.empty()) {
    // Capture the per-iteration continuation condition as a first-class map.
    // The forward recursive function then denotes the first stopping
    // iteration (or IterationCount if none stops) without adding cyclic CFG.
    std::string ContinueMapType = "[" + IterationType + "]bool";
    std::string ContinueIterationName =
        "$functional.read.continue.iteration." + std::to_string(Id);
    std::map<std::string, std::string> Capture;
    functionalCapture = &Capture;
    const Expr *ContinueBody =
        IsVerifier ? AssumptionsAt(Expr::id(ContinueIterationName))
                   : ContinueAt(Expr::id(ContinueIterationName));
    functionalCapture = nullptr;
    const Expr *ContinueMap = liftFunctionalMap(
        "$fl.lambda.continue." + std::to_string(proc->getId()) + "." +
            std::to_string(Id),
        {ContinueIterationName, IterationType}, ContinueBody, Capture,
        ContinueMapType, "smack.functional.continue");

    // firstStop(c, current, remaining) is the first iteration at or after
    // `current`, within `remaining` more, whose continuation predicate fails
    // (or current + remaining if none does). It is a recursive definition,
    // emitted as a bodiless function and its own definitional axiom rather
    // than as a function body, so the axiom can carry {:weight 0}: Boogie's
    // definitional axiom has weight 1, Z3 charges one generation per
    // unfolding and stops after about twenty, and Boogie reports the
    // resulting `unknown` as a definite error -- on a safe scan of a
    // 30-element array. A first-order characterisation (least k with
    // !c[k]) was tried and is exact but never instantiated at the right k;
    // the unfolding is what enumerates the iterations up to the stop. With a
    // constant trip count the chain is bounded by it; with a symbolic count
    // and a stop the solver cannot locate, the unfolding does not terminate
    // and the query times out, which is the honest outcome.
    std::string FirstStopName = "$functional.firstStop." +
                                std::to_string(proc->getId()) + "." +
                                std::to_string(Id);
    const std::string ContinuesName = "$continues";
    const std::string CurrentName = "$current";
    const std::string RemainingName = "$remaining";
    const Expr *Continues = Expr::id(ContinuesName);
    const Expr *Current = Expr::id(CurrentName);
    const Expr *Remaining = Expr::id(RemainingName);
    const Expr *One =
        rep->integerLit(1ULL, Summary.iterationType->getBitWidth());
    const Expr *Next =
        Expr::fn(indexedName("$add", {IterationType}), Current, One);
    const Expr *RemainingAfter =
        Expr::fn(indexedName("$sub", {IterationType}), Remaining, One);
    const Expr *Recursive =
        Expr::fn(FirstStopName, {Continues, Next, RemainingAfter});
    const Expr *FirstStopBody = Expr::ifThenElse(
        Expr::eq(Remaining, Zero), Current,
        Expr::ifThenElse(Expr::sel(Continues, Current), Recursive, Current));
    std::list<Binding> Params = {{ContinuesName, ContinueMapType},
                                 {CurrentName, IterationType},
                                 {RemainingName, IterationType}};
    const Expr *Application =
        Expr::fn(FirstStopName, {Continues, Current, Remaining});
    auto &Decls = rep->getProgram()->getDeclarations();
    Decls.push_back(Decl::function(FirstStopName, Params, IterationType));
    Decls.push_back(Decl::axiom(
        Expr::forall(Params,
                     {Attr::attr("qid", "smack.functional.firstStop"),
                      Attr::attr("weight", 0)},
                     Application, Expr::eq(Application, FirstStopBody))));
    FirstStop = Expr::fn(FirstStopName, {ContinueMap, Zero, IterationCount});
  }

  // One pointer-quantified fact per affine load, triggered by a read of that
  // load's map: for a pointer in the load's image, `Consequent` holds of the
  // iteration that reads it. Iteration-quantified facts alone are not enough
  // for the solver: their bound variable occurs only inside map indices, so
  // E-matching never instantiates them at the iteration a client read
  // concerns.
  auto TriggeredFacts =
      [&](const std::string &Tag,
          const std::function<const Expr *(const Expr *)> &Consequent) {
        SmallVector<const Expr *, 4> Facts;
        for (unsigned LoadIndex = 0; LoadIndex < Summary.loads.size();
             ++LoadIndex) {
          const FunctionalLoopLoad &Load = Summary.loads[LoadIndex];
          std::string LoadPath = rep->memPath(Load.load->getPointerOperand());
          std::string PointerName = "$functional.read.pointer." +
                                    std::to_string(Id) + "." +
                                    std::to_string(LoadIndex) + Tag;
          const Expr *Pointer = Expr::id(PointerName);
          const Expr *Start = functionalPointerSCEV(Load.access.start);
          const Expr *Delta = Expr::fn("$sub.ref", Pointer, Start);
          const Expr *DeltaAsInteger = Expr::fn(
              indexedName("$p2i", {Naming::PTR_TYPE, IterationType}), Delta);
          const Expr *Stride = rep->integerLit(
              static_cast<unsigned long long>(Load.access.stride),
              Summary.iterationType->getBitWidth());
          const Expr *Iteration =
              Expr::fn(rep->opName("$udiv", {Summary.iterationType}),
                       DeltaAsInteger, Stride);
          const Expr *IsReadAddress =
              Expr::eq(Pointer, functionalAddress(Load.access, Iteration,
                                                  Summary.iterationType));
          const Expr *InReadImage =
              Expr::and_(IterationInDomain(Iteration), IsReadAddress);
          const Expr *Trigger = rep->functionalLoad(
              Load.load->getPointerOperand(),
              Expr::id(CurrentMemories.at(LoadPath)), Pointer);
          Facts.push_back(
              Expr::forall({{PointerName, Naming::PTR_TYPE}}, Trigger,
                           Expr::impl(InReadImage, Consequent(Iteration))));
        }
        return Facts;
      };
  SmallVector<const Expr *, 4> TriggeredAllContinue =
      TriggeredFacts("", ContinueAt);

  // This is the semantic summary.  The pointer-quantified formula above is a
  // redundant consequence whose explicit load trigger lets clients instantiate
  // the fact at an arbitrary read address without inverting pointer arithmetic.
  std::string IterationName =
      "$functional.read.iteration." + std::to_string(Id);
  const Expr *ExactIteration = Expr::id(IterationName);
  const Expr *AllContinue =
      Expr::forall({{IterationName, IterationType}},
                   Expr::impl(IterationInDomain(ExactIteration),
                              ContinueAt(ExactIteration)));

  std::string VerifierKind = HasAssertion && HasAssumption ? "verifier "
                             : HasAssertion                ? "assertion "
                             : HasAssumption               ? "assumption "
                                                           : "";
  emit(Stmt::comment(std::string("functional read-only ") + VerifierKind +
                     "loop summary for " +
                     Summary.loop->getHeader()->getParent()->getName().str()));
  Block *Normal = createBlock();
  annotate(PreheaderBranch, Normal);
  Normal->addStmt(Stmt::assume(AllContinue));
  for (const Expr *Triggered : TriggeredAllContinue)
    Normal->addStmt(Stmt::assume(Triggered));
  Normal->addStmt(Stmt::goto_(
      {getBlock(IsVerifier ? Summary.exit : Summary.normalExit)->getName()}));

  std::list<std::string> Targets = {Normal->getName()};
  for (unsigned CheckIndex = 0; CheckIndex < Summary.accessChecks.size();
       ++CheckIndex) {
    const auto &Check = Summary.accessChecks[CheckIndex];
    std::string Suffix = std::to_string(Id) + "." + std::to_string(CheckIndex);
    std::string WitnessName = "$functional.read.check." + Suffix;
    proc->getDeclarations().push_back(
        Decl::variable(WitnessName, IterationType));
    const Expr *Witness = Expr::id(WitnessName);

    Block *CheckBlock = createBlock();
    annotate(PreheaderBranch, CheckBlock);
    CheckBlock->addStmt(Stmt::havoc(WitnessName));
    CheckBlock->addStmt(Stmt::assume(IterationInDomain(Witness)));
    if (FirstStop) {
      const Expr *BeforeStop =
          Expr::fn(indexedName("$ult", {IterationType, Naming::BOOL_TYPE}),
                   Witness, FirstStop);
      if (!IsVerifier) {
        CheckBlock->addStmt(
            Stmt::assume(Expr::or_(BeforeStop, Expr::eq(Witness, FirstStop))));
      } else {
        const Expr *PrecedingAssumptionsHold = Expr::lit(true);
        for (unsigned ActionIndex : Check.precedingAssumptions)
          PrecedingAssumptionsHold = Expr::and_(
              PrecedingAssumptionsHold,
              ActionAt(Summary.verifierActions[ActionIndex], Witness));
        const Expr *ExecutesAtStop =
            Expr::and_(Expr::eq(Witness, FirstStop), PrecedingAssumptionsHold);
        CheckBlock->addStmt(
            Stmt::assume(Expr::or_(BeforeStop, ExecutesAtStop)));
      }
    }
    annotate(*Check.call, CheckBlock);
    CheckBlock->addStmt(Stmt::call(
        Naming::MEMORY_SAFETY_FUNCTION,
        {functionalAddress(Check.access, Witness, Summary.iterationType),
         rep->pointerLit(static_cast<unsigned long long>(Check.size))}));
    CheckBlock->addStmt(Stmt::goto_({Normal->getName()}));
    Targets.push_back(CheckBlock->getName());
  }

  if (IsVerifier) {
    for (unsigned ActionIndex = 0; ActionIndex < Summary.verifierActions.size();
         ++ActionIndex) {
      const auto &Action = Summary.verifierActions[ActionIndex];
      if (Action.kind != FunctionalLoopVerifierAction::Kind::Assertion)
        continue;

      std::string Suffix =
          std::to_string(Id) + "." + std::to_string(ActionIndex);
      std::string WitnessName = "$functional.read.witness." + Suffix;
      proc->getDeclarations().push_back(
          Decl::variable(WitnessName, IterationType));
      const Expr *Witness = Expr::id(WitnessName);

      std::string PreviousName = "$functional.read.previous." + Suffix;
      const Expr *Previous = Expr::id(PreviousName);
      const Expr *BeforeWitness = Expr::and_(
          IterationInDomain(Previous),
          Expr::fn(indexedName("$ult", {IterationType, Naming::BOOL_TYPE}),
                   Previous, Witness));
      const Expr *EarlierIterationsPass =
          Expr::forall({{PreviousName, IterationType}},
                       Expr::impl(BeforeWitness, AllActionsAt(Previous)));
      // The same prefix, matchable from a read: without it a failed
      // assumption at an earlier iteration cannot be seen to block this
      // assertion, and the witness produces a spurious error.
      SmallVector<const Expr *, 4> EarlierIterationsPassTriggered =
          TriggeredFacts(".witness." + Suffix, [&](const Expr *Iteration) {
            return Expr::impl(Expr::fn(indexedName("$ult", {IterationType,
                                                            Naming::BOOL_TYPE}),
                                       Iteration, Witness),
                              AllActionsAt(Iteration));
          });

      const Expr *EarlierActionsPass = Expr::lit(true);
      for (unsigned Earlier = 0; Earlier < ActionIndex; ++Earlier)
        EarlierActionsPass =
            Expr::and_(EarlierActionsPass,
                       ActionAt(Summary.verifierActions[Earlier], Witness));
      const Expr *WitnessesFailure = Expr::and_(
          IterationInDomain(Witness),
          Expr::and_(EarlierIterationsPass,
                     Expr::and_(EarlierActionsPass,
                                Expr::not_(ActionAt(Action, Witness)))));

      Block *Failure = createBlock();
      annotate(PreheaderBranch, Failure);
      Failure->addStmt(Stmt::havoc(WitnessName));
      Failure->addStmt(Stmt::assume(WitnessesFailure));
      for (const Expr *Triggered : EarlierIterationsPassTriggered)
        Failure->addStmt(Stmt::assume(Triggered));
      annotate(*Action.call, Failure);
      Failure->addStmt(Stmt::assert_(Expr::lit(false)));
      Failure->addStmt(Stmt::goto_({getBlock(Summary.exit)->getName()}));
      Targets.push_back(Failure->getName());
    }
    emit(Stmt::goto_(Targets));
    return;
  }

  std::string WitnessName = "$functional.read.witness." + std::to_string(Id);
  proc->getDeclarations().push_back(Decl::variable(WitnessName, IterationType));
  const Expr *Witness = Expr::id(WitnessName);
  const Expr *WitnessesFailure =
      Expr::and_(IterationInDomain(Witness), Expr::not_(ContinueAt(Witness)));
  Block *Failure = createBlock();
  annotate(PreheaderBranch, Failure);
  Failure->addStmt(Stmt::havoc(WitnessName));
  Failure->addStmt(Stmt::assume(WitnessesFailure));
  Failure->addStmt(Stmt::goto_({getBlock(Summary.failureExit)->getName()}));
  Targets.push_back(Failure->getName());
  emit(Stmt::goto_(Targets));
}

void SmackInstGenerator::emitFunctionalLoop(
    const FunctionalLoopSummary &Summary) {
  unsigned Id = functionalLoopId++;
  std::map<std::string, const Value *> MemoryPointers;
  std::map<std::string, std::vector<const FunctionalLoopStore *>>
      StoresByMemory;
  for (const auto &Store : Summary.stores) {
    auto *StorePointer = Store.store->getPointerOperand();
    std::string Memory = rep->memPath(StorePointer);
    MemoryPointers[Memory] = StorePointer;
    StoresByMemory[Memory].push_back(&Store);
  }
  for (const auto &Load : Summary.loads)
    MemoryPointers[rep->memPath(Load.load->getPointerOperand())] =
        Load.load->getPointerOperand();

  std::map<std::string, std::string> EntryMemories;
  for (const auto &Memory : MemoryPointers) {
    std::string Snapshot =
        "$fl.entry." + std::to_string(Id) + "." + Memory.first;
    EntryMemories[Memory.first] = Snapshot;
    proc->getDeclarations().push_back(
        Decl::variable(Snapshot, rep->memType(Memory.second)));
    emit(Stmt::assign(Expr::id(Snapshot), Expr::id(Memory.first)));
  }

  std::string IterationType = rep->type(Summary.iterationType);
  auto Zero = rep->integerLit(0ULL, Summary.iterationType->getBitWidth());
  const Expr *IterationCount = functionalIntegerSCEV(Summary.iterationCount);

  if (!Summary.accessChecks.empty()) {
    Block *Update = createBlock();
    std::list<std::string> Targets = {Update->getName()};
    for (unsigned CheckIndex = 0; CheckIndex < Summary.accessChecks.size();
         ++CheckIndex) {
      const auto &Check = Summary.accessChecks[CheckIndex];
      std::string WitnessName = "$fl.check.iteration." + std::to_string(Id) +
                                "." + std::to_string(CheckIndex);
      proc->getDeclarations().push_back(
          Decl::variable(WitnessName, IterationType));
      const Expr *Witness = Expr::id(WitnessName);
      const Expr *InDomain = Expr::and_(
          Expr::fn(indexedName("$uge", {IterationType, Naming::BOOL_TYPE}),
                   Witness, Zero),
          Expr::fn(indexedName("$ult", {IterationType, Naming::BOOL_TYPE}),
                   Witness, IterationCount));
      if (Check.guard) {
        const Expr *Guard =
            functionalValue(Check.guard, Summary, Witness, EntryMemories);
        const Expr *GuardHolds = Expr::eq(Guard, rep->integerLit(1ULL, 1));
        InDomain = Expr::and_(
            InDomain, Check.guardValue ? GuardHolds : Expr::not_(GuardHolds));
      }

      Block *CheckBlock = createBlock();
      CheckBlock->addStmt(Stmt::havoc(WitnessName));
      CheckBlock->addStmt(Stmt::assume(InDomain));
      annotate(*Check.call, CheckBlock);
      CheckBlock->addStmt(Stmt::call(
          Naming::MEMORY_SAFETY_FUNCTION,
          {functionalAddress(Check.access, Witness, Summary.iterationType),
           rep->pointerLit(static_cast<unsigned long long>(Check.size))}));
      CheckBlock->addStmt(Stmt::goto_({Update->getName()}));
      Targets.push_back(CheckBlock->getName());
    }
    emit(Stmt::comment("functional affine access range checks"));
    emit(Stmt::goto_(Targets));
    currBlock = Update;
  }

  emit(Stmt::comment(
      "functional loop summary for " +
      Summary.stores.front().store->getFunction()->getName().str()));

  unsigned MemoryIndex = 0;
  for (const auto &MemoryStores : StoresByMemory) {
    const std::string &Destination = MemoryStores.first;
    std::string PointerName =
        "$fl.p." + std::to_string(Id) + "." + std::to_string(MemoryIndex);
    auto Pointer = Expr::id(PointerName);
    std::string MapType = rep->memType(MemoryPointers.at(Destination));
    std::map<std::string, std::string> Capture;
    functionalCapture = &Capture;
    // Rebuilt under capture: the iteration count may mention locals.
    const Expr *IterationCount = functionalIntegerSCEV(Summary.iterationCount);
    const Expr *Body = Expr::sel(
        functionalMap(EntryMemories.at(Destination), MapType), Pointer);

    // The recognizer proves these affine images pairwise disjoint, so their
    // ITE order is immaterial.  Every RHS and the default branch read only the
    // loop-entry snapshots.
    for (auto StoreIt = MemoryStores.second.rbegin();
         StoreIt != MemoryStores.second.rend(); ++StoreIt) {
      const FunctionalLoopStore &Store = **StoreIt;
      const AffineLoopAccess &Write = Store.access;
      const Expr *Start = functionalPointerSCEV(Write.start);
      auto Delta = Expr::fn("$sub.ref", Pointer, Start);
      auto DeltaAsInteger = Expr::fn(
          indexedName("$p2i", {Naming::PTR_TYPE, IterationType}), Delta);
      auto Iteration = Expr::fn(
          indexedName("$udiv", {IterationType}), DeltaAsInteger,
          rep->integerLit(static_cast<unsigned long long>(Write.stride),
                          Summary.iterationType->getBitWidth()));
      auto InDomain = Expr::and_(
          Expr::fn(indexedName("$uge", {IterationType, Naming::BOOL_TYPE}),
                   Iteration, Zero),
          Expr::fn(indexedName("$ult", {IterationType, Naming::BOOL_TYPE}),
                   Iteration, IterationCount));
      auto IsWrittenAddress = Expr::eq(
          Pointer, functionalAddress(Write, Iteration, Summary.iterationType));
      auto Predicate = Expr::and_(InDomain, IsWrittenAddress);
      if (Store.guard) {
        auto Guard =
            functionalValue(Store.guard, Summary, Iteration, EntryMemories);
        const Expr *GuardHolds = Expr::eq(Guard, rep->integerLit(1ULL, 1));
        if (!Store.guardValue)
          GuardHolds = Expr::not_(GuardHolds);
        Predicate = Expr::and_(Predicate, GuardHolds);
      }
      auto Value = functionalValue(Store.store->getValueOperand(), Summary,
                                   Iteration, EntryMemories);
      Body = Expr::ifThenElse(Predicate, Value, Body);
    }
    functionalCapture = nullptr;

    emit(Stmt::assign(
        Expr::id(Destination),
        liftFunctionalMap("$fl.lambda." + std::to_string(proc->getId()) + "." +
                              std::to_string(Id) + "." +
                              std::to_string(MemoryIndex++),
                          {PointerName, Naming::PTR_TYPE}, Body, Capture,
                          MapType, "smack.functional.write")));
  }
  const Expr *FinalInduction =
      functionalInductionValue(Summary, IterationCount);
  if (Summary.inductionEscapes) {
    // A direct use of the header PHI after the loop sees the value of the
    // last iteration that ran. When the exit test follows the body that is
    // one step short of the incremented value the exit PHIs carry.
    const Expr *ExitValue = FinalInduction;
    if (Summary.exitTestFollowsBody)
      ExitValue = functionalInductionValue(
          Summary,
          Expr::fn(
              indexedName("$sub", {IterationType}), IterationCount,
              rep->integerLit(1ULL, Summary.iterationType->getBitWidth())));
    emit(Stmt::assign(rep->expr(Summary.induction), ExitValue));
  }
  for (PHINode *Phi : Summary.finalInductionPhis)
    emit(Stmt::assign(rep->expr(Phi), FinalInduction));
  emit(Stmt::goto_({getBlock(Summary.exit)->getName()}));
}

const Stmt *
SmackInstGenerator::recordProcedureCall(const llvm::Value *V,
                                        std::list<const Attr *> attrs) {
  auto D = Decl::procedure("boogie_si_record_" + rep->type(V),
                           {{"x", rep->type(V)}});
  rep->addAuxiliaryDeclaration(D);
  return Stmt::call(D->getName(), {rep->expr(V)}, {}, attrs);
}

Block *SmackInstGenerator::createBlock() {
  Block *b = Block::block(naming->freshBlockName());
  proc->getBlocks().push_back(b);
  return b;
}

Block *SmackInstGenerator::getBlock(llvm::BasicBlock *bb) {
  if (blockMap.count(bb) == 0)
    blockMap[bb] = createBlock();
  return blockMap[bb];
}

void SmackInstGenerator::nameInstruction(llvm::Instruction &inst) {
  if (inst.getType()->isVoidTy())
    return;
  proc->getDeclarations().push_back(
      Decl::variable(naming->get(inst), rep->type(&inst)));
}

void SmackInstGenerator::annotate(llvm::Instruction &I, Block *B) {

  // do not generate sourceloc from calls to llvm.debug since
  // those point to variable declaration lines and such
  if (llvm::CallInst *ci = llvm::dyn_cast<llvm::CallInst>(&I)) {
    llvm::Function *f = ci->getCalledFunction();
    std::string name = f && f->hasName() ? f->getName().str() : "";
    if (name.find("llvm.dbg.") != std::string::npos) {
      return;
    }
  }

  if (SmackOptions::SourceLocSymbols && I.getMetadata("dbg")) {
    const DebugLoc DL = I.getDebugLoc();
    auto *scope = cast<DIScope>(DL.getScope());
    B->addStmt(Stmt::annot(Attr::attr("sourceloc", scope->getFilename().str(),
                                      DL.getLine(), DL.getCol())));
  }

  // https://stackoverflow.com/questions/22138947/reading-metadata-from-instruction
  SmallVector<std::pair<unsigned, MDNode *>, 4> MDForInst;
  I.getAllMetadata(MDForInst);
  SmallVector<StringRef, 8> Names;
  I.getModule()->getMDKindNames(Names);

  //  for(auto II = MDForInst.begin(), EE = MDForInst.end(); II !=EE; ++II) {
  for (auto II : MDForInst) {
    StringRef name = Names[II.first];
    if (name == "smack.memory.access" || name == "smack.memory.checked" ||
        name == "smack.loop.bound" || name == "verifier.primitive")
      continue;
    if (name.find("smack.") == 0 || name.find("verifier.") == 0) {
      std::list<const Expr *> attrs;
      for (auto AI = II.second->op_begin(), AE = II.second->op_end(); AI != AE;
           ++AI) {
        if (auto *CI = mdconst::dyn_extract<ConstantInt>(*AI)) {
          auto value = CI->getZExtValue();
          attrs.push_back(Expr::lit((long long)value));
        } else if (auto *CI = dyn_cast<MDString>(*AI)) {
          auto value = CI->getString();
          attrs.push_back(Expr::lit(value.str()));
        } else {
          llvm_unreachable("unexpected attribute type in smack metadata");
        }
      }
      B->addStmt(Stmt::annot(Attr::attr(name.str(), attrs)));
    }
  }
}

void SmackInstGenerator::processInstruction(llvm::Instruction &inst) {
  SDEBUG(errs() << "Inst: " << inst << "\n");
  annotate(inst, currBlock);
  ORIG(inst);
  nameInstruction(inst);
  nextInst++;
}

void SmackInstGenerator::visitBasicBlock(llvm::BasicBlock &bb) {
  nextInst = bb.begin();
  currBlock = getBlock(&bb);

  auto *F = bb.getParent();
  if (&bb == &F->getEntryBlock()) {
    for (auto &I : bb.getInstList()) {
      if (llvm::isa<llvm::DbgInfoIntrinsic>(I))
        continue;
      if (I.getDebugLoc()) {
        annotate(I, currBlock);
        break;
      }
    }
    if (SmackOptions::isEntryPoint(naming->get(*F))) {
      emit(recordProcedureCall(
          F, {Attr::attr("cexpr", "smack:entry:" + naming->get(*F))}));
      for (auto &A : F->args()) {
        emit(recordProcedureCall(
            &A, {Attr::attr("cexpr", "smack:arg:" + naming->get(*F) + ":" +
                                         naming->get(A))}));
      }
    }
  }
}

void SmackInstGenerator::visitInstruction(llvm::Instruction &inst) {
  SDEBUG(errs() << "Instruction not handled: " << inst << "\n");
  llvm_unreachable("Instruction not handled.");
}

void SmackInstGenerator::generatePhiAssigns(llvm::Instruction &ti) {
  llvm::BasicBlock *block = ti.getParent();
  std::list<const Expr *> lhs;
  std::list<const Expr *> rhs;
  for (unsigned i = 0; i < ti.getNumSuccessors(); i++) {

    // write to the phi-node variable of the successor
    for (llvm::BasicBlock::iterator s = ti.getSuccessor(i)->begin(),
                                    e = ti.getSuccessor(i)->end();
         s != e && llvm::isa<llvm::PHINode>(s); ++s) {

      llvm::PHINode *phi = llvm::cast<llvm::PHINode>(s);
      if (llvm::Value *v = phi->getIncomingValueForBlock(block)) {
        v = v->stripPointerCastsAndAliases();
        lhs.push_back(rep->expr(phi));
        rhs.push_back(rep->expr(v));
      }
    }
  }
  if (!lhs.empty()) {
    emit(Stmt::assign(lhs, rhs));
  }
}

void SmackInstGenerator::generateGotoStmts(
    llvm::Instruction &inst,
    std::vector<std::pair<const Expr *, llvm::BasicBlock *>> targets) {

  assert(targets.size() > 0);

  if (targets.size() > 1) {
    std::list<std::string> dispatch;

    for (unsigned i = 0; i < targets.size(); i++) {
      const Expr *condition = targets[i].first;
      llvm::BasicBlock *target = targets[i].second;

      if (target->getUniquePredecessor() == inst.getParent()) {
        Block *b = getBlock(target);
        b->insert(Stmt::assume(condition));
        dispatch.push_back(b->getName());

      } else {
        Block *b = createBlock();
        annotate(inst, b);
        b->addStmt(Stmt::assume(condition));
        b->addStmt(Stmt::goto_({getBlock(target)->getName()}));
        dispatch.push_back(b->getName());
      }
    }

    emit(Stmt::goto_(dispatch));

  } else
    emit(Stmt::goto_({getBlock(targets[0].second)->getName()}));
}

/******************************************************************************/
/*                 TERMINATOR                  INSTRUCTIONS                   */
/******************************************************************************/

void SmackInstGenerator::visitReturnInst(llvm::ReturnInst &ri) {
  processInstruction(ri);

  llvm::Value *v = ri.getReturnValue();
  if (v)
    emit(Stmt::assign(Expr::id(Naming::RET_VAR), rep->expr(v)));
  emit(Stmt::assign(Expr::id(Naming::EXN_VAR), Expr::lit(false)));
  emit(Stmt::return_());
}

void SmackInstGenerator::visitBranchInst(llvm::BranchInst &bi) {
  processInstruction(bi);

  auto Summary = summariesByPreheader.find(&bi);
  if (Summary != summariesByPreheader.end()) {
    if (Summary->second->kind != FunctionalLoopSummary::Kind::MemoryUpdate)
      emitReadOnlyFunctionalLoop(*Summary->second, bi);
    else
      emitFunctionalLoop(*Summary->second);
    return;
  }

  // Collect the list of tarets
  std::vector<std::pair<const Expr *, llvm::BasicBlock *>> targets;

  if (bi.getNumSuccessors() == 1) {

    // Unconditional branch
    targets.push_back({Expr::lit(true), bi.getSuccessor(0)});

  } else {

    // Conditional branch
    assert(bi.getNumSuccessors() == 2);
    const Expr *e =
        Expr::eq(rep->expr(bi.getCondition()), rep->integerLit(1ULL, 1));
    targets.push_back({e, bi.getSuccessor(0)});
    targets.push_back({Expr::not_(e), bi.getSuccessor(1)});
  }
  generatePhiAssigns(bi);
  if (bi.getNumSuccessors() > 1)
    emit(Stmt::annot(Attr::attr(Naming::BRANCH_CONDITION_ANNOTATION,
                                {rep->expr(bi.getCondition())})));
  generateGotoStmts(bi, targets);
}

void SmackInstGenerator::visitSwitchInst(llvm::SwitchInst &si) {
  processInstruction(si);

  // Collect the list of tarets
  std::vector<std::pair<const Expr *, llvm::BasicBlock *>> targets;

  const Expr *e = rep->expr(si.getCondition());
  const Expr *n = Expr::lit(true);

  for (llvm::SwitchInst::CaseIt i = si.case_begin(); i != si.case_begin();
       ++i) {

    const Expr *v = rep->expr(i->getCaseValue());
    targets.push_back({Expr::eq(e, v), i->getCaseSuccessor()});

    // Add the negation of this case to the default case
    n = Expr::and_(n, Expr::neq(e, v));
  }

  // The default case
  targets.push_back({n, si.getDefaultDest()});

  generatePhiAssigns(si);
  emit(Stmt::annot(Attr::attr(Naming::BRANCH_CONDITION_ANNOTATION,
                              {rep->expr(si.getCondition())})));
  generateGotoStmts(si, targets);
}

void SmackInstGenerator::visitInvokeInst(llvm::InvokeInst &ii) {
  processInstruction(ii);
  llvm::Function *f = ii.getCalledFunction();
  if (f)
    emit(rep->call(f, ii));
  else
    llvm_unreachable("Unexpected invoke instruction.");

  std::vector<std::pair<const Expr *, llvm::BasicBlock *>> targets;
  targets.push_back(
      {Expr::not_(Expr::id(Naming::EXN_VAR)), ii.getNormalDest()});
  targets.push_back({Expr::id(Naming::EXN_VAR), ii.getUnwindDest()});
  emit(Stmt::annot(Attr::attr(Naming::BRANCH_CONDITION_ANNOTATION,
                              {Expr::id(Naming::EXN_VAR)})));
  generateGotoStmts(ii, targets);
}

void SmackInstGenerator::visitResumeInst(llvm::ResumeInst &ri) {
  processInstruction(ri);
  emit(Stmt::assign(Expr::id(Naming::EXN_VAR), Expr::lit(true)));
  emit(Stmt::assign(Expr::id(Naming::EXN_VAL_VAR), rep->expr(ri.getValue())));
  emit(Stmt::return_());
}

void SmackInstGenerator::visitUnreachableInst(llvm::UnreachableInst &ii) {
  processInstruction(ii);

  emit(Stmt::assume(Expr::lit(false)));
}

/******************************************************************************/
/*                   BINARY                    OPERATIONS                     */
/******************************************************************************/

void SmackInstGenerator::visitBinaryOperator(llvm::BinaryOperator &I) {
  processInstruction(I);
  if (rep->isBitwiseOp(&I)) {
    auto T = I.getType();
    if (auto VT = dyn_cast<FixedVectorType>(T))
      T = VT->getElementType();
    if (T->isIntegerTy() && T->getIntegerBitWidth() > 1)
      SmackWarnings::warnOverApproximate(
          std::string("bitwise operation ") + I.getOpcodeName(),
          {&SmackOptions::BitPrecise}, currBlock, &I);
  }
  if (rep->isFpArithOp(&I))
    SmackWarnings::warnOverApproximate(
        std::string("floating-point operation ") + I.getOpcodeName(),
        {&SmackOptions::FloatEnabled}, currBlock, &I);

  const Expr *E;
  if (isa<FixedVectorType>(I.getType())) {
    auto X = I.getOperand(0);
    auto Y = I.getOperand(1);
    auto D = VectorOperations(rep).binary(&I);
    E = Expr::fn(D->getName(), {rep->expr(X), rep->expr(Y)});
  } else {
    E = rep->bop(&I);
  }
  emit(Stmt::assign(rep->expr(&I), E));
}

/******************************************************************************/
/*                   UNARY                    OPERATIONS                     */
/******************************************************************************/

void SmackInstGenerator::visitUnaryOperator(llvm::UnaryOperator &I) {
  assert(I.getOpcode() == Instruction::FNeg &&
         !isa<FixedVectorType>(I.getType()) && "Unsupported unary operation!");
  processInstruction(I);
  SmackWarnings::warnOverApproximate(
      std::string("floating-point operation ") + I.getOpcodeName(),
      {&SmackOptions::FloatEnabled}, currBlock, &I);
  emit(Stmt::assign(rep->expr(&I), rep->uop(&I)));
}

/******************************************************************************/
/*                   VECTOR                    OPERATIONS                     */
/******************************************************************************/

void SmackInstGenerator::visitExtractElementInst(ExtractElementInst &I) {
  processInstruction(I);
  auto X = I.getOperand(0);
  auto Y = I.getOperand(1);
  auto D = VectorOperations(rep).extract(X->getType(), Y->getType());
  emit(Stmt::assign(rep->expr(&I),
                    Expr::fn(D->getName(), {rep->expr(X), rep->expr(Y)})));
}

void SmackInstGenerator::visitInsertElementInst(InsertElementInst &I) {
  processInstruction(I);
  auto X = I.getOperand(0);
  auto Y = I.getOperand(1);
  auto Z = I.getOperand(2);
  auto D = VectorOperations(rep).insert(X->getType(), Z->getType());
  emit(Stmt::assign(
      rep->expr(&I),
      Expr::fn(D->getName(), {rep->expr(X), rep->expr(Y), rep->expr(Z)})));
}

void SmackInstGenerator::visitShuffleVectorInst(ShuffleVectorInst &I) {
  processInstruction(I);
  auto X = I.getOperand(0);
  auto Y = I.getOperand(1);
  auto M = I.getShuffleMask();
  std::vector<int> mask;
  for (auto idx : M)
    mask.push_back(idx);
  auto D = VectorOperations(rep).shuffle(X->getType(), I.getType(), mask);
  emit(Stmt::assign(rep->expr(&I),
                    Expr::fn(D->getName(), {rep->expr(X), rep->expr(Y)})));
}

/******************************************************************************/
/*                  AGGREGATE                   OPERATIONS                    */
/******************************************************************************/

void SmackInstGenerator::visitExtractValueInst(llvm::ExtractValueInst &evi) {
  processInstruction(evi);
  const Value *ao = evi.getAggregateOperand();
  const Expr *e = rep->expr(ao);
  const Type *t = ao->getType();

  for (auto &idx : evi.indices()) {
    e = Expr::fn(rep->opName(Naming::EXTRACT_VALUE, {getElemType(t, idx)}), e,
                 Expr::lit((unsigned long long)idx));
    t = getElemType(t, idx);
  }
  emit(Stmt::assign(rep->expr(&evi), e));
}

void SmackInstGenerator::visitInsertValueInst(llvm::InsertValueInst &ivi) {
  processInstruction(ivi);
  const Expr *old = rep->expr(ivi.getAggregateOperand());
  const Expr *res = rep->expr(&ivi);
  const llvm::Type *t = ivi.getType();

  auto getNumElements = [](const Type *t) -> unsigned {
    if (const llvm::StructType *st =
            llvm::dyn_cast<const llvm::StructType>(t)) {
      return st->getNumElements();
    } else if (const llvm::ArrayType *at =
                   llvm::dyn_cast<const llvm::ArrayType>(t)) {
      return at->getNumElements();
    } else {
      llvm_unreachable("Unexpected aggregate type.");
    }
  };

  for (auto &idx : ivi.indices()) {

    for (unsigned j = 0; j < getNumElements(t); j++) {
      if (j != idx) {
        emit(Stmt::assume(Expr::eq(
            Expr::fn(rep->opName(Naming::EXTRACT_VALUE, {getElemType(t, j)}),
                     res, Expr::lit(j)),
            Expr::fn(rep->opName(Naming::EXTRACT_VALUE, {getElemType(t, j)}),
                     old, Expr::lit(j)))));
      }
    }
    res = Expr::fn(rep->opName(Naming::EXTRACT_VALUE, {getElemType(t, idx)}),
                   res, Expr::lit(idx));
    old = Expr::fn(rep->opName(Naming::EXTRACT_VALUE, {getElemType(t, idx)}),
                   old, Expr::lit(idx));
    t = getElemType(t, idx);
  }
  emit(Stmt::assume(Expr::eq(res, rep->expr(ivi.getInsertedValueOperand()))));
}

/******************************************************************************/
/*     MEMORY       ACCESS        AND       ADDRESSING       OPERATIONS       */
/******************************************************************************/

void SmackInstGenerator::visitAllocaInst(llvm::AllocaInst &ai) {
  processInstruction(ai);
  emit(rep->alloca(ai));
}

void SmackInstGenerator::visitLoadInst(llvm::LoadInst &li) {
  processInstruction(li);
  auto P = li.getPointerOperand();
  auto T = dyn_cast<PointerType>(P->getType());
  assert(T && "expected pointer type");

  // TODO what happens with aggregate types?
  // assert (!li.getType()->isAggregateType() && "Unexpected load value.");

  const Expr *E;
  if (isa<FixedVectorType>(T->getPointerElementType())) {
    auto D = VectorOperations(rep).load(P);
    E = Expr::fn(D->getName(), {Expr::id(rep->memPath(P)), rep->expr(P)});
  } else {
    E = rep->load(P);
  }

  emit(Stmt::assign(rep->expr(&li), E));

  if (SmackOptions::MemoryModelDebug) {
    emit(Stmt::call(Naming::REC_MEM_OP, {Expr::id(Naming::MEM_OP_VAL)}));
    emit(recordProcedureCall(
        ConstantInt::get(Type::getInt32Ty(li.getContext()), 0), {}));
    emit(recordProcedureCall(P, {}));
    emit(recordProcedureCall(&li, {}));
  }
}

void SmackInstGenerator::visitStoreInst(llvm::StoreInst &si) {
  processInstruction(si);
  const llvm::Value *P = si.getPointerOperand();
  const llvm::Value *V = si.getValueOperand()->stripPointerCastsAndAliases();
  assert(!V->getType()->isAggregateType() && "Unexpected store value.");

  if (isa<FixedVectorType>(V->getType())) {
    auto D = VectorOperations(rep).store(P);
    auto M = Expr::id(rep->memPath(P));
    auto E = Expr::fn(D->getName(), {M, rep->expr(P), rep->expr(V)});
    emit(Stmt::assign(M, E));
  } else {
    emit(rep->store(P, V));
    if (const Stmt *inverseAssume = rep->inverseFPCastAssume(&si)) {
      emit(inverseAssume);
    }
  }

  if (SmackOptions::SourceLocSymbols) {
    if (const llvm::GlobalVariable *G =
            llvm::dyn_cast<const llvm::GlobalVariable>(P)) {
      if (const llvm::PointerType *t =
              llvm::dyn_cast<const llvm::PointerType>(G->getType())) {
        if (!t->getPointerElementType()->isPointerTy() && G->hasName()) {
          emit(recordProcedureCall(V,
                                   {Attr::attr("cexpr", G->getName().str())}));
        }
      }
    }
  }

  if (SmackOptions::MemoryModelDebug) {
    emit(Stmt::call(Naming::REC_MEM_OP, {Expr::id(Naming::MEM_OP_VAL)}));
    emit(recordProcedureCall(
        ConstantInt::get(Type::getInt32Ty(si.getContext()), 1), {}));
    emit(recordProcedureCall(P, {}));
    emit(recordProcedureCall(V, {}));
  }
}

void SmackInstGenerator::visitAtomicCmpXchgInst(llvm::AtomicCmpXchgInst &i) {
  processInstruction(i);
  const Expr *res = rep->expr(&i);
  const Expr *mem = rep->load(i.getOperand(0));
  const Expr *cmp = rep->expr(i.getOperand(1));
  const Expr *swp = rep->expr(i.getOperand(2));
  emit(Stmt::assign(res, mem));
  emit(rep->store(i.getOperand(0),
                  Expr::ifThenElse(Expr::eq(mem, cmp), swp, mem)));
}

void SmackInstGenerator::visitAtomicRMWInst(llvm::AtomicRMWInst &i) {
  using llvm::AtomicRMWInst;
  processInstruction(i);
  const Expr *res = rep->expr(&i);
  const Expr *mem = rep->load(i.getPointerOperand());
  const Expr *val = rep->expr(i.getValOperand());
  auto valT = rep->type(i.getValOperand()->getType());
  emit(Stmt::assign(res, mem));
  emit(rep->store(i.getPointerOperand(),
                  i.getOperation() == AtomicRMWInst::Xchg
                      ? val
                      : Expr::fn(indexedName(Naming::ATOMICRMWINST_TABLE.at(
                                                 i.getOperation()),
                                             {valT}),
                                 mem, val)));
}

void SmackInstGenerator::visitGetElementPtrInst(llvm::GetElementPtrInst &I) {
  processInstruction(I);
  emit(Stmt::assign(rep->expr(&I), rep->ptrArith(&I)));
}

/******************************************************************************/
/*                 CONVERSION                    OPERATIONS                   */
/******************************************************************************/

void SmackInstGenerator::visitCastInst(llvm::CastInst &I) {
  processInstruction(I);
  const Expr *E;
  if (isa<FixedVectorType>(I.getType())) {
    auto X = I.getOperand(0);
    auto D = VectorOperations(rep).cast(&I);
    E = Expr::fn(D->getName(), rep->expr(X));
  } else {
    E = rep->cast(&I);
  }
  emit(Stmt::assign(rep->expr(&I), E));

  if (I.getOpcode() == Instruction::BitCast) {
    if (const Stmt *inverseAssume =
            rep->inverseFPCastAssume(I.getOperand(0), I.getType())) {
      emit(inverseAssume);
    }
  }
}

/******************************************************************************/
/*                   OTHER                     OPERATIONS                     */
/******************************************************************************/

void SmackInstGenerator::visitCmpInst(llvm::CmpInst &I) {
  processInstruction(I);
  const Expr *E;
  if (isa<FixedVectorType>(I.getType())) {
    auto X = I.getOperand(0);
    auto Y = I.getOperand(1);
    auto D = VectorOperations(rep).cmp(&I);
    E = Expr::fn(D->getName(), rep->expr(X), rep->expr(Y));
  } else {
    E = rep->cmp(&I);
  }
  emit(Stmt::assign(rep->expr(&I), E));
}

void SmackInstGenerator::visitPHINode(llvm::PHINode &phi) {
  // NOTE: this is really a No-Op, since assignments to the phi nodes
  // are handled in the translation of branch/switch instructions.
  processInstruction(phi);
}

void SmackInstGenerator::visitSelectInst(llvm::SelectInst &i) {
  processInstruction(i);
  std::string x = naming->get(i);
  emit(Stmt::assign(Expr::id(x), rep->select(&i)));
}

void SmackInstGenerator::visitCallInst(llvm::CallInst &ci) {
  processInstruction(ci);

  if (ci.isInlineAsm()) {
    SmackWarnings::warnApproximate("inline asm call " + i2s(ci), currBlock,
                                   &ci);
    emit(Stmt::skip());
    return;
  }

  Function *f = ci.getCalledFunction();
  if (!f) {
    assert(ci.getCalledOperand() && "Called value is null");
    f = cast<Function>(ci.getCalledOperand()->stripPointerCastsAndAliases());
  }

  StringRef name = f->hasName() ? f->getName() : "";

  if (SmackOptions::RustPanics && name == Naming::RUST_PANIC_MARKER &&
      SmackOptions::shouldCheckFunction(
          ci.getParent()->getParent()->getName())) {
    // Convert Rust's panic functions into assertion violations
    emit(Stmt::assert_(Expr::lit(false),
                       {Attr::attr(Naming::RUST_PANIC_ANNOTATION)}));
  } else if (name == "__VERIFIER_assert" &&
             !SmackOptions::shouldCheckFunction(
                 ci.getParent()->getParent()->getName())) {
    // Skip this assertion if we shouldn't check in the parent function
    return;

  } else if (name.find(Naming::VALUE_PROC) != StringRef::npos) {
    emit(rep->valueAnnotation(ci));

  } else if (name.find(Naming::RETURN_VALUE_PROC) != StringRef::npos) {
    emit(rep->returnValueAnnotation(ci));

  } else if (name.find(Naming::MOD_PROC) != StringRef::npos) {
    proc->getModifies().push_back(rep->code(ci));

  } else if (name.find(Naming::CODE_PROC) != StringRef::npos) {
    emit(Stmt::code(rep->code(ci)));

  } else if (name.find(Naming::DECL_PROC) != StringRef::npos) {
    std::string code = rep->code(ci);
    proc->getDeclarations().push_back(Decl::code(code, code));

  } else if (name.find(Naming::TOP_DECL_PROC) != StringRef::npos) {
    std::string decl = rep->code(ci);
    rep->getProgram()->getDeclarations().push_back(Decl::code(decl, decl));
    if (VAR_DECL.match(decl)) {
      std::string var = VAR_DECL.sub("\\1", decl);
      rep->addBplGlobal(var);
    }

  } else if (rep->isContractExpr(f)) {
    // NOTE do not generate code for contract expressions

  } else if (name == "__CONTRACT_int_variable") {

    // TODO assume that all variables are within an expression scope (?)
    // emit(Stmt::assign(rep->expr(&ci),
    // Expr::id(rep->getString(ci.getArgOperand(0)))));

  } else if (name == Naming::CONTRACT_FORALL) {

    llvm_unreachable("universal quantifiers not implemented.");

    // assert(ci.arg_size() == 2
    //     && "Expected contract expression argument to contract function.");
    // CallInst* cj = dyn_cast<CallInst>(ci.getArgOperand(1));
    // assert(cj && "Expected contract expression argument to contract
    // function.");
    // Function* F = cj->getCalledFunction();
    // assert(F && rep->isContractExpr(F)
    //     && "Expected contract expression argument to contract function.");
    //
    // auto binding = rep->getString(ci.getArgOperand(0));
    // std::list<const Expr*> args;
    //
    // auto AX = F->getAttributes();
    // for (unsigned i = 0; i < cj->arg_size(); i++) {
    //   std::string var = "";
    //   if (AX.hasAttribute(i+1, "contract-var"))
    //     var = AX.getAttribute(i+1, "contract-var").getValueAsString();
    //   args.push_back(
    //     var == binding ? Expr::id(binding) :
    //     rep->expr(cj->getArgOperand(i)));
    // }
    // for (auto m : rep->memoryMaps())
    //   args.push_back(Expr::id(m.first));
    // auto E = Expr::fn(F->getName(), args);
    // emit(Stmt::assign(rep->expr(&ci),
    //   Expr::ifThenElse(Expr::forall(binding, "int", E),
    //     rep->integerLit(1U,1), rep->integerLit(0U,1))));

  } else if (name == Naming::CONTRACT_REQUIRES ||
             name == Naming::CONTRACT_ENSURES ||
             name == Naming::CONTRACT_INVARIANT) {

    assert(ci.arg_size() == 1 &&
           "Expected contract expression argument to contract function.");
    CallInst *cj = dyn_cast<CallInst>(ci.getArgOperand(0));
    assert(cj && "Expected contract expression argument to contract function.");
    Function *F = cj->getCalledFunction();
    assert(F && rep->isContractExpr(F) &&
           "Expected contract expression argument to contract function.");

    std::list<const Expr *> args;
    for (auto &V : cj->args())
      args.push_back(rep->expr(V));
    for (auto m : rep->memoryMaps())
      args.push_back(Expr::id(m.first));
    auto E = Expr::fn(F->getName().str(), args);
    if (name == Naming::CONTRACT_REQUIRES)
      proc->getRequires().push_back(E);
    else if (name == Naming::CONTRACT_ENSURES)
      proc->getEnsures().push_back(E);
    else {
      auto L = loops[ci.getParent()];
      assert(L);
      auto H = L->getHeader();
      assert(H && blockMap.count(H));
      blockMap[H]->getStatements().push_front(
          Stmt::assert_(E, {Attr::attr(Naming::LOOP_INVARIANT_ANNOTATION)}));
    }

    // } else if (name == "result") {
    //   assert(ci.arg_size() == 0 && "Unexpected operands to
    //   result.");
    //   emit(Stmt::assign(rep->expr(&ci),Expr::id(Naming::RET_VAR)));
    //
    // } else if (name == "qvar") {
    //   assert(ci.arg_size() == 1 && "Unexpected operands to qvar.");
    //   emit(Stmt::assign(rep->expr(&ci),Expr::id(rep->getString(ci.getArgOperand(0)))));
    //
    // } else if (name == "old") {
    //   assert(ci.arg_size() == 1 && "Unexpected operands to old.");
    //   llvm::LoadInst* LI =
    //   llvm::dyn_cast<llvm::LoadInst>(ci.getArgOperand(0));
    //   assert(LI && "Expected value from Load.");
    //   emit(Stmt::assign(rep->expr(&ci),
    //     Expr::fn("old",rep->load(LI->getPointerOperand())) ));

    // } else if (name == "forall") {
    //   assert(ci.arg_size() == 2 && "Unexpected operands to
    //   forall.");
    //   Value* var = ci.getArgOperand(0);
    //   Value* arg = ci.getArgOperand(1);
    //   Slice* S = getSlice(arg);
    //   emit(Stmt::assign(rep->expr(&ci),
    //     Expr::forall(rep->getString(var), "int",
    //     S->getBoogieExpression(naming,rep))));
    //
    // } else if (name == "exists") {
    //   assert(ci.arg_size() == 2 && "Unexpected operands to
    //   forall.");
    //   Value* var = ci.getArgOperand(0);
    //   Value* arg = ci.getArgOperand(1);
    //   Slice* S = getSlice(arg);
    //   emit(Stmt::assign(rep->expr(&ci),
    //     Expr::exists(rep->getString(var), "int",
    //     S->getBoogieExpression(naming,rep))));
    //
    // } else if (name == "invariant") {
    //   assert(ci.arg_size() == 1 && "Unexpected operands to
    //   invariant.");
    //   Slice* S = getSlice(ci.getArgOperand(0));
    //   emit(Stmt::assert_(S->getBoogieExpression(naming,rep)));

  } else {
    emit(rep->call(f, ci));
  }

  if (f->isDeclaration()) {
    std::string name = naming->get(*f);
    if (!EXTERNAL_PROC_IGNORE.match(name) && rep->isExternal(&ci))
      emit(Stmt::assume(Expr::fn(Naming::EXTERNAL_ADDR, rep->expr(&ci))));
  }

  if ((naming->get(*f).find("__SMACK") == 0 ||
       naming->get(*f).find("__VERIFIER") == 0) &&
      !f->getReturnType()->isVoidTy()) {
    emit(recordProcedureCall(
        &ci, {Attr::attr("cexpr", "smack:ext:" + naming->get(*f))}));
  }
}

void SmackInstGenerator::visitCallBrInst(llvm::CallBrInst &cbi) {
  processInstruction(cbi);
  SmackWarnings::warnApproximate("callbr instruction " + i2s(cbi), currBlock,
                                 &cbi);
  emit(Stmt::skip());
}

bool isSourceLoc(const Stmt *stmt) {
  return (stmt->getKind() == Stmt::ASSUME &&
          (llvm::cast<const AssumeStmt>(stmt))->hasAttr("sourceloc")) ||
         (stmt->getKind() == Stmt::CALL);
}

void SmackInstGenerator::visitDbgValueInst(llvm::DbgValueInst &dvi) {
  processInstruction(dvi);

  if (SmackOptions::SourceLocSymbols) {
    Value *V = dvi.getValue();
    const llvm::DILocalVariable *var = dvi.getVariable();
    // if (V && !V->getType()->isPointerTy() && !llvm::isa<ConstantInt>(V)) {
    if (V && !V->getType()->isPointerTy()) {
      // if (currBlock->begin() != currBlock->end()
      //&& currBlock->getStatements().back()->getKind() == Stmt::ASSUME) {
      //    && isSourceLoc(currBlock->getStatements().back())) {
      // assert(&*currInst == &dvi && "Current Instruction mismatch!");
      auto currInst = std::prev(nextInst);
      if (currInst != dvi.getParent()->begin()) {
        const Instruction &pi = *std::prev(currInst);
        V = V->stripPointerCastsAndAliases();
        if (!llvm::isa<const PHINode>(&pi) &&
            V == llvm::dyn_cast<const Value>(&pi))
          emit(recordProcedureCall(
              V, {Attr::attr("cexpr", var->getName().str())}));
      }
      Function *F = dvi.getFunction();
      for (auto &arg : F->args()) {
        if (&arg == V && var->getScope() == F->getMetadata("dbg")) {
          emit(recordProcedureCall(
              V, {Attr::attr("cexpr", naming->get(*F) +
                                          ":arg:" + var->getName().str())}));
          break;
        }
      }
    }
  }
}

void SmackInstGenerator::visitLandingPadInst(llvm::LandingPadInst &lpi) {
  processInstruction(lpi);
  // TODO what exactly!?
  emit(Stmt::assign(rep->expr(&lpi), Expr::id(Naming::EXN_VAL_VAR)));
  if (lpi.isCleanup())
    emit(Stmt::assign(Expr::id(Naming::EXN_VAR), Expr::lit(false)));
  SmackWarnings::warnApproximate("landingpad clauses", currBlock, &lpi);
}

/******************************************************************************/
/*                  INTRINSIC                    FUNCTIONS                    */
/******************************************************************************/

void SmackInstGenerator::visitMemCpyInst(llvm::MemCpyInst &mci) {
  processInstruction(mci);
  emit(rep->memcpy(mci));
}

void SmackInstGenerator::visitMemSetInst(llvm::MemSetInst &msi) {
  processInstruction(msi);
  emit(rep->memset(msi));
}

void SmackInstGenerator::visitIntrinsicInst(llvm::IntrinsicInst &ii) {
  processInstruction(ii);

  //(CallInst -> Void) -> [Flags] -> (CallInst -> Void)
  static const auto conditionalModel =
      [this](std::function<void(CallInst *)> modelGenFunc,
             std::initializer_list<const cl::opt<bool> *> requiredFlags,
             SmackWarnings::FlagRelation rel =
                 SmackWarnings::FlagRelation::And) {
        auto unsetFlags = SmackWarnings::getUnsetFlags(requiredFlags);
        auto satisfied = SmackWarnings::isSatisfied(requiredFlags, rel);
        return [this, unsetFlags, modelGenFunc, satisfied, rel](CallInst *ci) {
          if (satisfied)
            modelGenFunc(ci);
          else {
            SmackWarnings::warnOverApproximate(
                "call to " + ci->getCalledFunction()->getName().str(),
                unsetFlags, currBlock, ci, rel);
            emit(rep->call(ci->getCalledFunction(), *ci));
          }
        };
      };

  // Optionally generate a boogie assume statement from assume statements in
  // LLVM. Currently this behavior is experimental and must be enabled by
  // passing the -llvm-assumes flag. The default behavior of this
  // function is to ignore the assume statement, specified by the "none"
  // argument. If the check argument is given, an additional assertion is
  // generated to check the validity of the assumption.
  static const auto assume = [this](CallInst *ci) {
    if (SmackOptions::LLVMAssumes != LLVMAssumeType::none) {
      auto arg = rep->expr(ci->getArgOperand(0));
      auto llvmTrue =
          SmackOptions::BitPrecise ? Expr::lit(1, 1) : Expr::lit(1LL);
      auto chkStmt = Expr::eq(arg, llvmTrue);
      if (SmackOptions::LLVMAssumes == LLVMAssumeType::check &&
          SmackOptions::shouldCheckFunction(ci->getFunction()->getName()))
        emit(Stmt::assert_(chkStmt));
      else
        emit(Stmt::assume(chkStmt));
    } else {
      // Skip assume statements
      return;
    }
  };

  static const auto f16UpCast = conditionalModel(
      [this](CallInst *ci) {
        // translation: $f := $fpext.bvhalf.*($rmode, $bitcast.bv16.bvhalf($i));
        auto argT = rep->type(ci->getArgOperand(0)->getType());
        auto retT = rep->type(ci->getFunctionType()->getReturnType());
        emit(Stmt::assign(
            rep->expr(ci),
            Expr::fn(
                indexedName("$fpext", {Naming::HALF_TYPE, retT}),
                {Expr::id(Naming::RMODE_VAR),
                 Expr::fn(indexedName("$bitcast", {argT, Naming::HALF_TYPE}),
                          rep->expr(ci->getArgOperand(0)))})));
      },
      {&SmackOptions::FloatEnabled, &SmackOptions::BitPrecise});

  static const auto f16DownCast = conditionalModel(
      [this](CallInst *ci) {
        // translation: assume($bitcast.bv16.bvhalf($i) ==
        // $fptrunc.bvfloat.bvhalf($rmode, $f));
        auto argT = rep->type(ci->getArgOperand(0)->getType());
        auto retT = rep->type(ci->getFunctionType()->getReturnType());
        emit(Stmt::assume(Expr::eq(
            Expr::fn(indexedName("$fptrunc", {argT, Naming::HALF_TYPE}),
                     Expr::id(Naming::RMODE_VAR),
                     rep->expr(ci->getArgOperand(0))),
            Expr::fn(indexedName("$bitcast", {retT, Naming::HALF_TYPE}),
                     rep->expr(ci)))));
      },
      {&SmackOptions::FloatEnabled, &SmackOptions::BitPrecise});

  static const auto fma = conditionalModel(
      [this](CallInst *ci) {
        emit(Stmt::assign(
            rep->expr(ci),
            Expr::fn(indexedName(
                         "$fma",
                         {rep->type(ci->getFunctionType()->getReturnType())}),
                     rep->expr(ci->getArgOperand(0)),
                     rep->expr(ci->getArgOperand(1)),
                     rep->expr(ci->getArgOperand(2)))));
      },
      {&SmackOptions::FloatEnabled});

  static const auto bitreverse = [this](Value *arg) {
    auto width = arg->getType()->getIntegerBitWidth();
    auto var = rep->expr(arg);

    // Swap the bits to the right and left of the middle
    const Expr *body;
    if (width % 2 == 0) {
      body = Expr::bvConcat(Expr::bvExtract(var, width / 2, width / 2 - 1),
                            Expr::bvExtract(var, width / 2 + 1, width / 2));
    } else {
      body = Expr::bvExtract(var, width / 2 + 1, width / 2);
    }
    // Swap the bits to the right and the left of the already swapped portion.
    unsigned offset = width & 1;
    for (unsigned i = width % 2 == 0 ? 1 : 0; i < width / 2; ++i) {
      body = Expr::bvConcat(
          Expr::bvConcat(Expr::bvExtract(var, width / 2 - i, width / 2 - i - 1),
                         body),
          Expr::bvExtract(var, width / 2 + i + 1 + offset,
                          width / 2 + i + offset));
    }
    return body;
  };

  static const auto bswap = [this](Value *arg) {
    auto width = arg->getType()->getIntegerBitWidth();
    auto var = rep->expr(arg);

    // Swap the bytes to the right and left of the middle
    const Expr *body =
        Expr::bvConcat(Expr::bvExtract(var, width / 2, width / 2 - 8),
                       Expr::bvExtract(var, width / 2 + 8, width / 2));

    // Swap the bytes to the right and the left of the already swapped portion.
    for (unsigned i = 8; i < width / 2; i += 8) {
      body = Expr::bvConcat(
          Expr::bvConcat(Expr::bvExtract(var, width / 2 - i, width / 2 - i - 8),
                         body),
          Expr::bvExtract(var, width / 2 + i + 8, width / 2 + i));
    }
    return body;
  };

  // Count leading zeros
  static const auto ctlz = conditionalModel(
      [this](CallInst *ci) {
        auto width = ci->getArgOperand(0)->getType()->getIntegerBitWidth();
        auto var = rep->expr(ci->getArgOperand(0));

        // e.g., if v[32:31] == 1 then 0bv32 else if v[31:30] == 1 then 1bv32
        // else
        // ... else if v[1:0] == 1 then 31bv32 else 32bv32
        const Expr *body = Expr::lit(width, width);
        for (unsigned i = 0; i < width; ++i) {
          body = Expr::ifThenElse(
              Expr::eq(Expr::bvExtract(var, i + 1, i), Expr::lit(1, 1)),
              Expr::lit(width - i - 1, width), body);
        }

        // Handle the is_zero_undef case, i.e. if the flag is set and the
        // argument
        // is zero, then the result is undefined.
        auto isZeroUndef = rep->expr(ci->getArgOperand(1));
        body =
            Expr::ifThenElse(Expr::and_(Expr::eq(isZeroUndef, Expr::lit(1, 1)),
                                        Expr::eq(var, Expr::lit(0, width))),
                             rep->expr(ci), // The result is undefined
                             body);
        emit(Stmt::havoc(rep->expr(ci)));
        emit(Stmt::assign(rep->expr(ci), body));
      },
      {&SmackOptions::BitPrecise});

  // Count trailing zeros
  static const auto cttz = conditionalModel(
      [this](CallInst *ci) {
        auto width = ci->getArgOperand(0)->getType()->getIntegerBitWidth();
        auto arg = rep->expr(ci->getArgOperand(0));

        // e.g., if v[1:0] == 1 then 0bv32 else if v[2:1] == 1 then 1bv32 else
        // ... else if v[32:31] == 1 then 31bv32 else 32bv32
        const Expr *body = Expr::lit(width, width);
        for (unsigned i = width; i > 0; --i) {
          body = Expr::ifThenElse(
              Expr::eq(Expr::bvExtract(arg, i, i - 1), Expr::lit(1, 1)),
              Expr::lit(i - 1, width), body);
        }

        // Handle the is_zero_undef case, i.e. if the flag is set and the
        // argument
        // is zero, then the result is undefined.
        auto isZeroUndef = rep->expr(ci->getArgOperand(1));
        body =
            Expr::ifThenElse(Expr::and_(Expr::eq(isZeroUndef, Expr::lit(1, 1)),
                                        Expr::eq(arg, Expr::lit(0, width))),
                             rep->expr(ci), // The result is undefined
                             body);
        emit(Stmt::havoc(rep->expr(ci)));
        emit(Stmt::assign(rep->expr(ci), body));
      },
      {&SmackOptions::BitPrecise});

  // Count the population of 1s in a bv
  static const auto ctpop = conditionalModel(
      [this](CallInst *ci) {
        Value *arg = ci->getArgOperand(0);
        auto width = arg->getType()->getIntegerBitWidth();
        auto var = rep->expr(arg);
        const Expr *body = nullptr;
        auto type = rep->type(arg->getType());

        if (SmackOptions::BitPrecise) { // Bitvector mode
          body = Expr::lit(0, width);
          for (unsigned i = 0; i < width; ++i) {
            body = Expr::fn(indexedName("$add", {type}),
                            Expr::fn(indexedName("$zext", {"bv1", type}),
                                     Expr::bvExtract(var, i + 1, i)),
                            body);
          }
        } else { // Otherwise, try with the integer encoding
          body = Expr::lit(0ull);
          for (unsigned i = 0; i < width; ++i) {
            auto quotient =
                Expr::fn(indexedName("$udiv", {type}), var,
                         Expr::lit((unsigned long long)(1ull << i)));
            auto remainder = Expr::fn(indexedName("$urem", {type}), quotient,
                                      Expr::lit(2ull));
            body = Expr::fn(indexedName("$add", {type}), remainder, body);
          }
        }
        emit(Stmt::assign(rep->expr(ci), body));
      },
      {&SmackOptions::BitPrecise, &SmackOptions::RewriteBitwiseOps},
      SmackWarnings::FlagRelation::Or);

  static const auto assignBvExpr =
      [this](std::function<const Expr *(Value *)> exprGenFunc) {
        return conditionalModel(
            [this, exprGenFunc](CallInst *ci) {
              emit(Stmt::assign(rep->expr(ci),
                                exprGenFunc(ci->getArgOperand(0))));
            },
            {&SmackOptions::BitPrecise});
      };

  static const auto assignUnFPFuncApp = [this](std::string fnBase) {
    return conditionalModel(
        [this, fnBase](CallInst *ci) {
          // translation: $res := $<func>.bv*($arg1);
          emit(Stmt::assign(
              rep->expr(ci),
              Expr::fn(
                  indexedName(fnBase,
                              {rep->type(ci->getArgOperand(0)->getType())}),
                  rep->expr(ci->getArgOperand(0)))));
        },
        {&SmackOptions::FloatEnabled});
  };

  static const auto assignBinFPFuncApp = [this](std::string fnBase) {
    return conditionalModel(
        [this, fnBase](CallInst *ci) {
          // translation: $res := $<func>.bv*($arg1, $arg2);
          emit(Stmt::assign(
              rep->expr(ci),
              Expr::fn(indexedName(
                           fnBase,
                           {rep->type(ci->getFunctionType()->getReturnType())}),
                       {rep->expr(ci->getArgOperand(0)),
                        rep->expr(ci->getArgOperand(1))})));
        },
        {&SmackOptions::FloatEnabled});
  };

  static const auto copysign = conditionalModel(
      [this](CallInst *ci) {
        // translation:
        //   if !$isnan.bv*($arg2) {
        //     $res := ite($isnegative.bv*($arg1) !=
        //                 $isnegative.bv*($arg2),
        //                 $fneg.bv*($arg1), $arg1);
        //   }
        // SMT-LIB has a single NaN value, while C permits NaNs with either
        // sign. When $arg2 is NaN, overapproximate the result sign instead
        // of treating $isnegative.bv*($arg2) as precise.
        auto type = rep->type(ci->getFunctionType()->getReturnType());
        auto boolType = Naming::BOOL_TYPE;
        auto x = rep->expr(ci->getArgOperand(0));
        auto y = rep->expr(ci->getArgOperand(1));
        auto result = rep->expr(ci);
        auto isNegFn = indexedName("$isnegative", {type, boolType});
        auto isNanFn = indexedName("$isnan", {type, boolType});
        auto negX = Expr::fn(indexedName("$fneg", {type}), x);
        auto signDiff = Expr::neq(Expr::fn(isNegFn, x), Expr::fn(isNegFn, y));
        auto precise = Expr::ifThenElse(signDiff, negX, x);
        auto isNanX = Expr::fn(isNanFn, x);
        auto isNanY = Expr::fn(isNanFn, y);
        auto isNanResult = Expr::fn(isNanFn, result);
        auto nanSignResult = Expr::ifThenElse(
            isNanX, isNanResult,
            Expr::or_(Expr::eq(result, x), Expr::eq(result, negX)));
        emit(Stmt::havoc(result));
        emit(Stmt::assume(Expr::ifThenElse(isNanY, nanSignResult,
                                           Expr::eq(result, precise))));
      },
      {&SmackOptions::FloatEnabled});

  // Expr* -> (CallInst -> Void)
  static const auto assignRoundFPFuncApp = [this](const Expr *rMode) {
    return conditionalModel(
        [this, rMode](CallInst *ci) {
          emit(Stmt::assign(
              rep->expr(ci),
              Expr::fn(indexedName(
                           "$round",
                           {rep->type(ci->getFunctionType()->getReturnType())}),
                       {rMode, rep->expr(ci->getArgOperand(0))})));
        },
        {&SmackOptions::FloatEnabled});
  };

  static const auto identity = [this](CallInst *ci) {
    // translation: $res := $arg1
    Value *val = ci->getArgOperand(0);
    emit(Stmt::assign(rep->expr(ci), rep->expr(val)));
  };

  static const auto ignore = [this](CallInst *ci) { emit(Stmt::skip()); };

  // TODO: these functions is consistent with the implementations in math.c,
  // meaning we can use __builtin_* to implement math.c which is mostly
  // modeled using __SMACK_code.

  static const std::map<llvm::Intrinsic::ID, std::function<void(CallInst *)>>
      stmtMap{
          {llvm::Intrinsic::assume, assume},
          {llvm::Intrinsic::bitreverse, assignBvExpr(bitreverse)},
          {llvm::Intrinsic::bswap, assignBvExpr(bswap)},
          {llvm::Intrinsic::convert_from_fp16, f16UpCast},
          {llvm::Intrinsic::convert_to_fp16, f16DownCast},
          {llvm::Intrinsic::ctlz, ctlz},
          {llvm::Intrinsic::ctpop, ctpop},
          {llvm::Intrinsic::cttz, cttz},
          {llvm::Intrinsic::dbg_declare, ignore},
          {llvm::Intrinsic::dbg_label, ignore},
          {llvm::Intrinsic::copysign, copysign},
          {llvm::Intrinsic::expect, identity},
          {llvm::Intrinsic::fabs, assignUnFPFuncApp("$abs")},
          {llvm::Intrinsic::fma, fma},
          {llvm::Intrinsic::sqrt, assignUnFPFuncApp("$sqrt")},
          {llvm::Intrinsic::maxnum, assignBinFPFuncApp("$max")},
          {llvm::Intrinsic::minnum, assignBinFPFuncApp("$min")},
          {llvm::Intrinsic::ceil,
           assignRoundFPFuncApp(Expr::lit(RModeKind::RTP))},
          {llvm::Intrinsic::floor,
           assignRoundFPFuncApp(Expr::lit(RModeKind::RTN))},
          {llvm::Intrinsic::nearbyint,
           assignRoundFPFuncApp(Expr::id(Naming::RMODE_VAR))},
          {llvm::Intrinsic::rint,
           assignRoundFPFuncApp(Expr::id(Naming::RMODE_VAR))},
          {llvm::Intrinsic::round,
           assignRoundFPFuncApp(Expr::lit(RModeKind::RNA))},
          {llvm::Intrinsic::trunc,
           assignRoundFPFuncApp(Expr::lit(RModeKind::RTZ))}
          // TODO: in future versions, there may be intrinsics that round floats
          // to integers like lround
      };

  auto it = stmtMap.find(ii.getIntrinsicID());
  if (it != stmtMap.end())
    it->second(&ii);
  else if (ii.getCalledFunction()->getName().startswith(
               "llvm.experimental.constrained.")) {
    SmackWarnings::warnApproximate(ii.getCalledFunction()->getName().str(),
                                   currBlock, &ii);
    if (!ii.getType()->isVoidTy())
      emit(Stmt::havoc(rep->expr(&ii)));
    else
      emit(Stmt::skip());
  } else if (ii.getIntrinsicID() ==
             llvm::Intrinsic::experimental_noalias_scope_decl) {
    // Ignore this function as we cannot handle arguments of metadata type.
  } else {
    SmackWarnings::warnApproximate(ii.getCalledFunction()->getName().str(),
                                   currBlock, &ii);
    emit(rep->call(ii.getCalledFunction(), ii));
  }
}

} // namespace smack
