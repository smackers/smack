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

const bool SKIP_INCOMPLETE_NODES = false;

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

  // TODO what to do when there are no potential targets?
  if (Targets.size())
    new UnreachableInst (M->getContext(), failBB);
  else
    ReturnInst::Create(M->getContext(), failBB);

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
// Method: makeDirectCall()
//
// Description:
//  Transform the specified call site into a direct call.
//
// Inputs:
//  CS - The call site to transform.
//
// Preconditions:
//  1) This method assumes that CS is an indirect call site.
//  2) This method assumes that a pointer to the CallTarget analysis pass has
//     already been acquired by the class.
//
void
Devirtualize::makeDirectCall (CallBase *CS) {
  //
  // Find the targets of the indirect function call.
  //

  std::vector<const Function*> Targets;

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
    for (unsigned i=0; i<CI->getNumArgOperands(); i++) {
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
    for (unsigned i=0; i<CI->getNumArgOperands(); i++)
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
  // Second, we will only transform those call sites which are complete (i.e.,
  // for which we know all of the call targets).
  //
  if (SKIP_INCOMPLETE_NODES && !CCG->isComplete(*CS))
    return;

  //
  // This is an indirect call site.  Put it in the worklist of call sites to
  // transforms.
  //
  Worklist.push_back(CS);
  return;
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
  // Get the targets of indirect function calls.
  //
  CCG = &getAnalysis<seadsa::CompleteCallGraph>();

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
  // need transforming.
  //
  for (unsigned index = 0; index < Worklist.size(); ++index) {
    // Autobots, transform (the call site)!
    makeDirectCall (Worklist[index]);
  }

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
INITIALIZE_PASS_END(Devirtualize, "devirt", "Devirtualize indirect function calls", false, false)
