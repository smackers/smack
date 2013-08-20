//===- Devirt.cpp - Devirtualize using the sig match intrinsic in llva ----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "devirt"

#include "assistDS/Devirt.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/ADT/Statistic.h"

#include <iostream>
#include <algorithm>
#include <iterator>

using namespace llvm;

// Pass ID variable
char Devirtualize::ID = 0;

// Pass statistics
STATISTIC(FuncAdded, "Number of bounce functions added");
STATISTIC(CSConvert, "Number of call sites converted");

// Pass registration
RegisterPass<Devirtualize>
X ("devirt", "Devirtualize indirect function calls");

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
castTo (Value * V, Type * Ty, std::string Name, Instruction * InsertPt) {
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
  return CastInst::CreateZExtOrBitCast (V, Ty, Name, InsertPt);
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
Devirtualize::findInCache (const CallSite & CS,
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
    if (CS.getType() != bounceFunc->getReturnType())
      continue;

    // Check the type of the function pointer and the arguments
    if (CS.getCalledValue()->stripPointerCasts()->getType() !=
        bounceFunc->arg_begin()->getType())
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
Devirtualize::buildBounce (CallSite CS, std::vector<const Function*>& Targets) {
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
  Value* ptr = CS.getCalledValue();
  std::vector<Type *> TP;
  TP.insert (TP.begin(), ptr->getType());
  for (CallSite::arg_iterator i = CS.arg_begin();
       i != CS.arg_end();
       ++i) {
    TP.push_back ((*i)->getType());
  }

  FunctionType* NewTy = FunctionType::get(CS.getType(), TP, false);
  Module * M = CS.getInstruction()->getParent()->getParent()->getParent();
  Function* F = Function::Create (NewTy,
                                  GlobalValue::InternalLinkage,
                                  "devirtbounce",
                                  M);

  //
  // Set the names of the arguments.  Also, record the arguments in a vector
  // for subsequence access.
  //
  F->arg_begin()->setName("funcPtr");
  std::vector<Value*> fargs;
  for(Function::arg_iterator ai = F->arg_begin(), ae = F->arg_end(); ai != ae; ++ai)
    if (ai != F->arg_begin()) {
      fargs.push_back(ai);
      ai->setName("arg");
    }

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

    // Create the basic block for doing the direct call
    BasicBlock* BL = BasicBlock::Create (M->getContext(), FL->getName(), F);
    targets[FL] = BL;
    // Create the direct function call
    Value* directCall = CallInst::Create (const_cast<Function*>(FL),
                                          fargs,
                                          "",
                                          BL);

    // Add the return instruction for the basic block
    if (CS.getType()->isVoidTy())
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
  Value * FArg = castTo (F->arg_begin(), VoidPtrType, "", InsertPt);
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
  //InsertPt->setUnconditionalDest (tailBB);
  InsertPt->setSuccessor(0, tailBB);
  InsertPt->setSuccessor(1, tailBB);
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
Devirtualize::makeDirectCall (CallSite & CS) {
  //
  // Find the targets of the indirect function call.
  //

  //
  // Convert the call site if there were any function call targets found.
  //
  if (CTF->size(CS)) {
    std::vector<const Function*> Targets;
    Targets.insert (Targets.begin(), CTF->begin(CS), CTF->end(CS));
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
    if (CallInst* CI = dyn_cast<CallInst>(CS.getInstruction())) {
      std::vector<Value*> Params (CI->op_begin(), CI->op_end());
      std::string name = CI->hasName() ? CI->getName().str() + ".dv" : "";
      CallInst* CN = CallInst::Create (const_cast<Function*>(NF),
                                       Params,
                                       name,
                                       CI);
      CI->replaceAllUsesWith(CN);
      CI->eraseFromParent();
    } else if (InvokeInst* CI = dyn_cast<InvokeInst>(CS.getInstruction())) {
      std::vector<Value*> Params (CI->op_begin(), CI->op_end());
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
  }

  return;
}

//
// Method: visitCallSite()
//
// Description:
//  Examine the specified call site.  If it is an indirect call, mark it for
//  transformation into a direct call.
//
void
Devirtualize::visitCallSite (CallSite &CS) {
  //
  // First, determine if this is a direct call.  If so, then just ignore it.
  //
  Value * CalledValue = CS.getCalledValue();
  if (isa<Function>(CalledValue->stripPointerCasts()))
    return;

  //
  // Second, we will only transform those call sites which are complete (i.e.,
  // for which we know all of the call targets).
  //
  if (!(CTF->isComplete(CS)))
    return;

  //
  // This is an indirect call site.  Put it in the worklist of call sites to
  // transforms.
  //
  Worklist.push_back (CS.getInstruction());
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
  CTF = &getAnalysis<dsa::CallTargetFinder<EQTDDataStructures> >();

  //
  // Get information on the target system.
  //
  //
  TD = &getAnalysis<DataLayout>();

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
    CallSite CS (Worklist[index]);
    makeDirectCall (CS);
  }

  //
  // Conservatively assume that we've changed one or more call sites.
  //
  return true;
}

