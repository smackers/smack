//===- Devirt.cpp - Devirtualize using the sig match intrinsic in llva ----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "devirt"

#include "utils/Devirt.h"

#include "smack/Debug.h"
#include "seadsa/InitializePasses.hh"
#include "utils/InitializePasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/ADT/Statistic.h"

#include <iostream>
#include <algorithm>
#include <iterator>

using namespace llvm;

// Pass statistics
STATISTIC(FuncAdded, "Number of bounce functions added");
STATISTIC(CSConvert, "Number of call sites converted");
STATISTIC(CSNoOp, "Number of call sites turned into no-ops");

// The name of the no-op stubs.  It has to start with "devirtbounce" so that the
// trace post-processing keeps skipping the calls that this pass introduces
// (see share/smack/svcomp/toSVCOMPformat.py).
static const char *NOOP_STUB_NAME = "devirtbounce_noop";

static llvm::cl::opt<DevirtMode> DispatchMode(
    "devirt-mode",
    llvm::cl::desc("Dispatch policy for indirect function calls"),
    llvm::cl::values(
        clEnumValN(DevirtMode::All, "all",
                   "dispatch every indirect call, falling back to all "
                   "address-taken functions with a compatible signature "
                   "when the targets are unknown (default)"),
        clEnumValN(DevirtMode::Known, "known",
                   "dispatch an indirect call only when its targets are "
                   "known; turn every other indirect call into a no-op")),
    llvm::cl::init(DevirtMode::All));

//
// Function: getVoidPtrType()
//
// Description:
//  Return a pointer to the LLVM type for a void pointer.
//
// Return value:
//  A pointer to an LLVM type for the void pointer.
//
static inline
PointerType * getVoidPtrType (LLVMContext & C) {
  Type * Int8Type  = IntegerType::getInt8Ty(C);
  return PointerType::getUnqual(Int8Type);
}

//
// Function: castTo()
//
// Description:
//  Given an LLVM value, insert a cast instruction to make it a given type.
//
static inline Value *
castTo (Value * V, Type * Ty, std::string Name, Value * InsertPt) {
  //
  // Don't bother creating a cast if it's already the correct type.
  //
  if (V->getType() == Ty)
    return V;

  //
  // If it's a constant, just create a constant expression.
  //
  if (Constant * C = dyn_cast<Constant>(V)) {
    Constant * CE = ConstantExpr::getZExtOrBitCast (C, Ty);
    return CE;
  }

  //
  // Otherwise, insert a cast instruction.
  //
  if (auto I = dyn_cast<Instruction>(InsertPt))
    return CastInst::CreateZExtOrBitCast (V, Ty, Name, I);
  else if (auto B = dyn_cast<BasicBlock>(InsertPt))
    return CastInst::CreateZExtOrBitCast (V, Ty, Name, B);
  else
    llvm_unreachable("Unexpected insertion point.");

}

static inline bool isZExtOrBitCastable(Value* V, Type* T) {
  return CastInst::castIsValid(Instruction::ZExt, V->getType(), T) ||
         CastInst::castIsValid(Instruction::BitCast, V->getType(), T);
}

static inline bool match(CallBase *CS, const Function &F) {
  auto N = CS->arg_size();
  auto T = F.getFunctionType();
  auto M = T->getNumParams();
  auto RT = T->getReturnType();
  auto IT = CS->getType();

  if (RT != IT && !CastInst::isBitCastable(RT, IT))
    return false;

  if (N < M)
    return false;

  if (N > M && !F.isVarArg())
    return false;

  for (unsigned i=0; i<M; i++) {
    auto A = CS->getArgOperand(i);
    auto PT = T->getParamType(i);
    if (A->getType() != PT && !isZExtOrBitCastable(A, PT))
      return false;
  }

  return true;
}

static inline bool checkArgs(const CallBase *CS, const Function *F) {
  auto N = CS->arg_size();
  auto T = F->getFunctionType();
  auto M = T->getNumParams();

  if (N + 1 != M)
    return false;

  for (unsigned i=0; i<N; i++) {
    auto A = CS->getArgOperand(i);
    auto PT = T->getParamType(i+1);
    if (A->getType() != PT && !isZExtOrBitCastable(A, PT))
      return false;
  }
  return true;
}

//
// Function: refersOnlyToGlobals()
//
// Description:
//  Determine whether every allocation site of the given node is a global
//  value.  The allocation sites of a node over-approximate the objects that a
//  pointer to that node may refer to, so a node whose allocation sites are all
//  globals cannot hold the address of a stack or heap object, nor an address
//  that was synthesized out of an integer.
//
static bool refersOnlyToGlobals(const seadsa::Node *N) {
  const auto &AllocSites = N->getAllocSites();

  //
  // A node without any allocation site tells us nothing about what the pointer
  // refers to, so it does not count as known.
  //
  if (AllocSites.empty())
    return false;

  for (const Value *V : AllocSites) {
    const Value *Site = V->stripPointerCastsAndAliases();
    //
    // The resolver of an ifunc runs at load time, so the function it selects
    // is not known statically.
    //
    if (!isa<GlobalValue>(Site) || isa<GlobalIFunc>(Site))
      return false;
  }

  return true;
}

//
// Method: findInCache()
//
// Description:
//  This method looks through the cache of bounce functions to see if there
//  exists a bounce function for the specified call site.
//
// Return value:
//  0 - No usable bounce function has been created.
//  Otherwise, a pointer to a bounce that can replace the call site is
//  returned.
//
const Function *
Devirtualize::findInCache (const CallBase *CS,
                           std::set<const Function*>& Targets) {
  //
  // Iterate through all of the existing bounce functions to see if one of them
  // can be resued.
  //
  std::map<const Function *, std::set<const Function *> >::iterator I;
  for (I = bounceCache.begin(); I != bounceCache.end(); ++I) {
    //
    // If the bounce function and the function pointer have different types,
    // then skip this bounce function because it is incompatible.
    //
    const Function * bounceFunc = I->first;

    // Check the return type
    if (CS->getType() != bounceFunc->getReturnType())
      continue;

    // Check the type of the function pointer and the argumentsa
    PointerType* PT = dyn_cast<PointerType>(bounceFunc->arg_begin()->getType());
    assert(PT);
    if (CS->getCalledOperand()->stripPointerCastsAndAliases()->getType() != PT)
      continue;

    FunctionType* FT = dyn_cast<FunctionType>(PT->getElementType());
    assert(FT);
    if (FT->isVarArg() && !checkArgs(CS, bounceFunc))
      continue;

    //
    // Determine whether the targets are identical.  If so, then this function
    // can be used as a bounce function for this call site.
    //
    if (Targets == I->second)
      return I->first;
  }

  //
  // No suiteable bounce function was found.
  //
  return 0;
}

//
// Method: buildBounce()
//
// Description:
//  Replaces the given call site with a call to a bounce function.  The
//  bounce function compares the function pointer to one of the given
//  target functions and calls the function directly if the pointer
//  matches.
//
Function*
Devirtualize::buildBounce (CallBase *CS, std::vector<const Function*>& Targets) {
  //
  // Update the statistics on the number of bounce functions added to the
  // module.
  //
  ++FuncAdded;
  //
  // Create a bounce function that has a function signature almost identical
  // to the function being called.  The only difference is that it will have
  // an additional pointer argument at the beginning of its argument list that
  // will be the function to call.
  //
  Value* ptr = CS->getCalledOperand();
  std::vector<Type *> TP;
  TP.insert (TP.begin(), ptr->getType());
  for (auto i = CS->arg_begin();
       i != CS->arg_end();
       ++i) {
    TP.push_back ((*i)->getType());
  }

  FunctionType* NewTy = FunctionType::get(CS->getType(), TP, false);
  Module * M = CS->getParent()->getParent()->getParent();
  Function* F = Function::Create (NewTy,
                                  GlobalValue::InternalLinkage,
                                  "devirtbounce",
                                  M);

  //
  // Set the names of the arguments.
  //
  F->arg_begin()->setName("funcPtr");
  for (auto A = std::next(F->arg_begin()), E = F->arg_end(); A != E; ++A)
    A->setName("arg");

  //
  // Create an entry basic block for the function.  All it should do is perform
  // some cast instructions and branch to the first comparison basic block.
  //
  BasicBlock* entryBB = BasicBlock::Create (M->getContext(), "entry", F);

  //
  // For each function target, create a basic block that will call that
  // function directly.
  //
  std::map<const Function*, BasicBlock*> targets;
  for (unsigned index = 0; index < Targets.size(); ++index) {
    const Function* FL = Targets[index];
    const FunctionType* FT = FL->getFunctionType();

    // Create the basic block for doing the direct call
    BasicBlock* BL = BasicBlock::Create (M->getContext(), FL->getName(), F);
    targets[FL] = BL;
    // Create the direct function call

    std::vector<Value*> Args;
    Function::arg_iterator P, PE;
    FunctionType::param_iterator T, TE;
    for (P = std::next(F->arg_begin()), PE = F->arg_end(),
         T = FT->param_begin(), TE = FT->param_end();
         P != PE && T != TE; ++P, ++T)
      Args.push_back(castTo(&*P, *T, "", BL));

    Value* directCall = CallInst::Create (const_cast<Function*>(FL),
                                          Args,
                                          "",
                                          BL);

    // Add the return instruction for the basic block
    if (CS->getType()->isVoidTy())
      ReturnInst::Create (M->getContext(), BL);
    else
      ReturnInst::Create (M->getContext(), directCall, BL);
  }

  //
  // Create a failure basic block.  This basic block should simply be an
  // unreachable instruction.
  //
  BasicBlock * failBB = BasicBlock::Create (M->getContext(),
                                            "fail",
                                            F);

  //
  // The bounce function is only built for a call site whose targets are known,
  // so the function pointer matching none of them cannot happen.
  //
  new UnreachableInst (M->getContext(), failBB);

  //
  // Setup the entry basic block.  For now, just have it call the failure
  // basic block.  We'll change the basic block to which it branches later.
  //
  BranchInst * InsertPt = BranchInst::Create (failBB, entryBB);

  //
  // Create basic blocks which will test the value of the incoming function
  // pointer and branch to the appropriate basic block to call the function.
  //
  Type * VoidPtrType = getVoidPtrType (M->getContext());
  Value * FArg = castTo (&*F->arg_begin(), VoidPtrType, "", InsertPt);
  BasicBlock * tailBB = failBB;
  for (unsigned index = 0; index < Targets.size(); ++index) {
    //
    // Cast the function pointer to an integer.  This can go in the entry
    // block.
    //
    Value * TargetInt = castTo (const_cast<Function*>(Targets[index]),
                                VoidPtrType,
                                "",
                                InsertPt);

    //
    // Create a new basic block that compares the function pointer to the
    // function target.  If the function pointer matches, we'll branch to the
    // basic block performing the direct call for that function; otherwise,
    // we'll branch to the next function call target.
    //
    BasicBlock* TB = targets[Targets[index]];
    BasicBlock* newB = BasicBlock::Create (M->getContext(),
                                           "test." + Targets[index]->getName(),
                                           F);
    CmpInst * setcc = CmpInst::Create (Instruction::ICmp,
                                       CmpInst::ICMP_EQ,
                                       TargetInt,
                                       FArg,
                                       "sc",
                                       newB);
    BranchInst::Create (TB, tailBB, setcc, newB);

    //
    // Make this newly created basic block the next block that will be reached
    // when the next comparison will need to be done.
    //
    tailBB = newB;
  }

  //
  // Make the entry basic block branch to the first comparison basic block.
  //
  InsertPt->setSuccessor(0, tailBB);
  //
  // Return the newly created bounce function.
  //
  return F;
}

//
// Method: getCalleeNode()
//
// Description:
//  Return the sea-dsa node of the function pointer of the given call site, or
//  null when the points-to analysis has nothing to say about it.
//
const seadsa::Node *
Devirtualize::getCalleeNode (const CallBase *CS) {
  assert(DSA && "the points-to analysis is required in this dispatch mode");

  const Function *Caller = CS->getFunction();
  if (!Caller || !DSA->hasGraph(*Caller))
    return nullptr;

  //
  // Note that getCell() asserts that the value has a cell, so hasCell() has to
  // be consulted first.
  //
  seadsa::Graph &G = DSA->getGraph(*Caller);
  const Value *Callee = CS->getCalledOperand();
  if (!Callee || !G.hasCell(*Callee))
    return nullptr;

  return G.getCell(*Callee).getNode();
}

//
// Method: hasKnownTargets()
//
// Description:
//  Determine whether the targets of the given indirect call site are known,
//  and collect them into Targets when they are.  The targets are known when
//  the sea-dsa node of the function pointer is complete -- no code outside of
//  the module could have written into it -- and refers only to global values.
//
// Return value:
//  true  - The call site can be dispatched; Targets holds its targets.
//  false - The targets are unknown; Targets is left empty.
//
bool
Devirtualize::hasKnownTargets (CallBase *CS,
                               std::vector<const Function*>& Targets) {
  SDEBUG(errs() << "[devirt] call site: " << *CS << "\n");

  const seadsa::Node *N = getCalleeNode(CS);
  if (!N) {
    SDEBUG(errs() << "[devirt]   unknown: no node for the function pointer\n");
    return false;
  }

  SDEBUG(errs() << "[devirt]   node marks: "
                << N->getNodeType().toStr() << "\n");

  //
  // A node that was reached through an inttoptr holds an address that was
  // synthesized out of an integer, so its allocation sites say nothing about
  // what it refers to.
  //
  if (N->isIntToPtr()) {
    SDEBUG(errs() << "[devirt]   unknown: the node is marked inttoptr\n");
    return false;
  }

  //
  // An external node came out of code that is not part of the module, which
  // may have stored an arbitrary function pointer into it.  Its allocation
  // sites are therefore only a lower bound on what the function pointer may
  // refer to.  Note that this, rather than the incomplete mark, is what
  // sea-dsa itself uses to decide that a call site is fully resolved: nothing
  // ever sets the incomplete mark at the moment.  The mark is consulted
  // anyway so that this stays correct if that ever changes.
  //
  if (N->isExternal() || N->isIncomplete()) {
    SDEBUG(errs() << "[devirt]   unknown: the node is not complete\n");
    return false;
  }

  if (!refersOnlyToGlobals(N)) {
    SDEBUG(errs() << "[devirt]   unknown: the node refers to "
                  << (N->getAllocSites().empty() ? "nothing known"
                                                 : "a non-global")
                  << "\n");
    return false;
  }

  for (const Value *V : N->getAllocSites())
    if (auto F = dyn_cast<Function>(V->stripPointerCastsAndAliases()))
      if (match(CS, *F))
        Targets.push_back(F);

  //
  // The allocation sites are stored in a set ordered by address, so sort the
  // targets to keep the generated code independent of the memory layout.
  //
  std::sort(Targets.begin(), Targets.end(),
            [](const Function *A, const Function *B) {
              if (A->getName() != B->getName())
                return A->getName() < B->getName();
              return A < B;
            });

  //
  // The node may well refer to globals none of which is a function that can be
  // called here, in which case there is nothing to dispatch to.
  //
  if (Targets.empty()) {
    SDEBUG(errs() << "[devirt]   unknown: no global the node refers to is a "
                     "function with a compatible signature\n");
    return false;
  }

  SDEBUG(for (const Function *F : Targets) {
    errs() << "[devirt]   target: " << F->getName() << "\n";
  });
  return true;
}

//
// Method: findTargets()
//
// Description:
//  Collect the targets to dispatch the given indirect call site to, following
//  the dispatch policy that was selected on the command line.
//
// Return value:
//  true  - The call site should be dispatched to Targets.
//  false - The call site should be turned into a no-op.
//
bool
Devirtualize::findTargets (CallBase *CS,
                           std::vector<const Function*>& Targets) {
  if (DispatchMode == DevirtMode::Known)
    return hasKnownTargets(CS, Targets);

  // TODO should we allow non-matching targets?
  // TODO non-matching targets leads to crashes in bounce creation
  if (CCG->isComplete(*CS)) {
    for (auto F = CCG->begin(*CS); F != CCG->end(*CS); ++F)
      if (match(CS, **F))
        Targets.push_back(*F);
  } else {
    for (auto &F : *CS->getParent()->getParent()->getParent())
      if (F.hasAddressTaken() && match(CS, F))
        Targets.push_back(&F);
  }

  //
  // A bounce function without any target would fall through to its failure
  // basic block, which cannot return a value of the expected type.  Treat such
  // a call site as a no-op instead.
  //
  return !Targets.empty();
}

//
// Method: getNoOpStub()
//
// Description:
//  Return a parameterless function returning the given type, to stand in for
//  the call sites that are not dispatched.  The stub is deliberately left
//  undefined: SMACK translates a call to an undefined procedure into one that
//  havocs the value it returns and modifies nothing, which is precisely the
//  intended no-op semantics.
//
Function*
Devirtualize::getNoOpStub (Type *RetTy, Module &M) {
  auto It = noopCache.find(RetTy);
  if (It != noopCache.end())
    return It->second;

  FunctionType *NoOpTy = FunctionType::get(RetTy, {}, false);
  Function *F = Function::Create(NoOpTy, GlobalValue::ExternalLinkage,
                                 NOOP_STUB_NAME, &M);
  noopCache[RetTy] = F;
  return F;
}

//
// Method: makeNoOpCall()
//
// Description:
//  Replace the given call site with a call to a no-op stub.  The arguments are
//  dropped on purpose: were they passed on to the stub, the points-to analysis
//  that SMACK runs afterwards would treat the objects they point to as escaping
//  to external code, which would coarsen the memory model of the whole module.
//
// Inputs:
//  CS - The call site to transform.
//
void
Devirtualize::makeNoOpCall (CallBase *CS) {
  Module *M = CS->getModule();
  Function *NoOp = getNoOpStub(CS->getType(), *M);

  std::string name = CS->hasName() ? CS->getName().str() + ".dv" : "";
  Instruction *NC;
  if (isa<CallInst>(CS)) {
    NC = CallInst::Create(NoOp, {}, name, CS);
  } else {
    InvokeInst *II = cast<InvokeInst>(CS);
    NC = InvokeInst::Create(NoOp, II->getNormalDest(), II->getUnwindDest(),
                            {}, name, II);
  }

  //
  // Keep the source location so that the call site is still attributed to the
  // line it came from.
  //
  NC->setDebugLoc(CS->getDebugLoc());

  if (!CS->getType()->isVoidTy())
    CS->replaceAllUsesWith(NC);
  CS->eraseFromParent();

  ++CSNoOp;

  return;
}

//
// Method: makeDirectCall()
//
// Description:
//  Transform the specified call site into a direct call.
//
// Inputs:
//  CS      - The call site to transform.
//  Targets - The functions to dispatch the call site to; must not be empty.
//
// Preconditions:
//  1) This method assumes that CS is an indirect call site.
//
void
Devirtualize::makeDirectCall (CallBase *CS,
                              std::vector<const Function*>& Targets) {
  assert(!Targets.empty() && "Cannot dispatch a call site without targets.");

  //
  // Determine if an existing bounce function can be used for this call site.
  //
  std::set<const Function *> targetSet (Targets.begin(), Targets.end());
  const Function * NF = findInCache (CS, targetSet);

  //
  // If no cached bounce function was found, build a function which will
  // implement a switch statement.  The switch statement will determine which
  // function target to call and call it.
  //
  if (!NF) {
    // Build the bounce function and add it to the cache
    NF = buildBounce (CS, Targets);
    bounceCache[NF] = targetSet;
  }

  //
  // Replace the original call with a call to the bounce function.
  //
  if (CallInst* CI = dyn_cast<CallInst>(CS)) {
    std::vector<Value*> Params;
    Params.push_back(CI->getCalledOperand());
    for (unsigned i=0; i<CI->arg_size(); i++) {
      Params.push_back(
        castTo(CI->getArgOperand(i), NF->getFunctionType()->getParamType(i+1), "", CS)
      );
    }

    std::string name = CI->hasName() ? CI->getName().str() + ".dv" : "";
    CallInst* CN = CallInst::Create (const_cast<Function*>(NF),
                                       Params,
                                       name,
                                       CI);
    CI->replaceAllUsesWith(CN);
    CI->eraseFromParent();
  } else if (InvokeInst* CI = dyn_cast<InvokeInst>(CS)) {
    std::vector<Value*> Params;
    Params.push_back(CI->getCalledOperand());
    for (unsigned i=0; i<CI->arg_size(); i++)
      Params.push_back(
        castTo(CI->getArgOperand(i), NF->getFunctionType()->getParamType(i+1), "", CS)
      );
    std::string name = CI->hasName() ? CI->getName().str() + ".dv" : "";
    InvokeInst* CN = InvokeInst::Create(const_cast<Function*>(NF),
                                        CI->getNormalDest(),
                                        CI->getUnwindDest(),
                                        Params,
                                        name,
                                        CI);
    CI->replaceAllUsesWith(CN);
    CI->eraseFromParent();
  }

  //
  // Update the statistics on the number of transformed call sites.
  //
  ++CSConvert;

  return;
}

//
// Method: processCallSite()
//
// Description:
//  Examine the specified call site.  If it is an indirect call, mark it for
//  transformation into a direct call.
//
void
Devirtualize::processCallSite (CallBase *CS) {
  //
  // First, determine if this is a direct call.  If so, then just ignore it.
  //
  if (!CS->isIndirectCall())
    return;

  //
  // This is an indirect call site.  Put it in the worklist of call sites to
  // transforms.
  //
  Worklist.push_back(CS);
  return;
}

//
// Method: getAnalysisUsage()
//
// Description:
//  Request the analysis that the selected dispatch policy relies on.  Each
//  policy pays only for the analysis it uses.
//
void
Devirtualize::getAnalysisUsage (AnalysisUsage &AU) const {
  if (DispatchMode == DevirtMode::Known)
    AU.addRequired<seadsa::DsaAnalysis>();
  else
    AU.addRequired<seadsa::CompleteCallGraph>();
}

//
// Method: runOnModule()
//
// Description:
//  Entry point for this LLVM transform pass.  Look for indirect function calls
//  and turn them into direct function calls.
//
bool
Devirtualize::runOnModule (Module & M) {
  //
  // Get the analysis telling us the targets of indirect function calls.
  //
  if (DispatchMode == DevirtMode::Known) {
    DSA = &getAnalysis<seadsa::DsaAnalysis>().getDsaAnalysis();
    assert(DSA->kind() == seadsa::GlobalAnalysisKind::CONTEXT_INSENSITIVE &&
           "Currently we only want the context-insensitive sea-dsa.");
  } else {
    CCG = &getAnalysis<seadsa::CompleteCallGraph>();
  }

  //
  // Get information on the target system.
  //
  //
  TD = &M.getDataLayout();

  // Visit all of the call instructions in this function and record those that
  // are indirect function calls.
  //
  visit (M);

  //
  // Now go through and transform all of the indirect calls that we found that
  // need transforming.  A call site whose targets are unknown becomes a no-op.
  //
  unsigned NumNoOps = 0;
  for (unsigned index = 0; index < Worklist.size(); ++index) {
    // Autobots, transform (the call site)!
    CallBase *CS = Worklist[index];
    std::vector<const Function*> Targets;
    if (findTargets(CS, Targets)) {
      makeDirectCall (CS, Targets);
    } else {
      makeNoOpCall (CS);
      ++NumNoOps;
    }
  }
  Worklist.clear();

  //
  // Dropping a call is an under-approximation, so say so rather than silently
  // verifying less of the program than the user asked for.
  //
  if (NumNoOps)
    errs() << "SMACK warning: " << NumNoOps
           << " indirect call site(s) with unknown targets were replaced by "
              "no-ops.\n";

  //
  // Conservatively assume that we've changed one or more call sites.
  //
  return true;
}

// Pass ID variable
char Devirtualize::ID = 0;

using namespace seadsa;
// Pass registration
INITIALIZE_PASS_BEGIN(Devirtualize, "devirt", "Devirtualize indirect function calls", false, false)
INITIALIZE_PASS_DEPENDENCY(CompleteCallGraph)
INITIALIZE_PASS_DEPENDENCY(DsaAnalysis)
INITIALIZE_PASS_END(Devirtualize, "devirt", "Devirtualize indirect function calls", false, false)
