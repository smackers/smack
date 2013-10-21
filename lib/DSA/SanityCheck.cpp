//===- SanityCheck.cpp - Check sanity and consistency of DSA results ------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Perform a sanity check on the DSA results.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "dsa-check"

#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"

using namespace llvm;

//
// Class: CheckSanity
//
// Description:
//  This is an LLVM pass that will request DSA results and then do some sanity
//  checks on the DSA results.
//
class SanityCheck : public ModulePass {
  public:
    static char ID;
    SanityCheck() : ModulePass (ID) {
      dsaPass = 0;
    }
    virtual bool runOnModule(Module &M);
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<EQTDDataStructures>();
      AU.setPreservesAll();
    }

  protected:
    void checkLoad (LoadInst & LI);

    // The DSA pass which is to be sanitized
    DataStructures * dsaPass;
};

// Sanity Check Pass ID
char SanityCheck::ID = 0;

static RegisterPass<SanityCheck>
X("dsa-check", "Check consistency of Data Structure Analysis");

//
// Method: checkLoad()
//
// Description:
//  This method ensures that the DSNode associated with the result of a load
//  instruction is linked from the DSNode associated with the pointer
//  dereferenced by the load.
//
void
SanityCheck::checkLoad (LoadInst & LI) {
  //
  // Get the DSA Graph for the function in which the load instruction lives.
  //
  Function * F = LI.getParent()->getParent();
  DSGraph * G = dsaPass->getDSGraph (*F);

  //
  // Get the DSNode information for both the result of the load instruction
  // and its pointer operand.  If the result of the load has no DSNode, then
  // nothing needs to be done.
  //
  DSNode* ResultNode = G->getNodeForValue (&LI).getNode();
  DSNode* PtrNode    = G->getNodeForValue (LI.getPointerOperand()).getNode();
  if (!ResultNode) {
    return;
  }
  assert (PtrNode && "Load operand has no DSNode!\n");

  //
  // Scan through the links of the DSNode of the load's pointer operand; we
  // need to determine the offset into the memory object from which the result
  // of the load is loaded.
  //
  DSNode::LinkMapTy::iterator linki = PtrNode->edge_begin();
#ifndef NDEBUG
  bool found = false;
#endif
  for (; linki != PtrNode->edge_end(); ++linki) {
    DSNodeHandle & LinkNode = linki->second;
    if (LinkNode.getNode() == ResultNode) {
#ifndef NDEBUG
      found = true;
#endif
    }
  }

  assert (found && "Can't find link for load result!\n");
  return;
}

//
// Method: runOnModule()
//
// Description:
//  This method is the entry point for the sanity checking pass.
//
// Inputs:
//  M - The LLVM module which should be analyzed for sanity and consistency.
//
// Return value:
//  false - The Module has not been modified (this pass should never modify the
//          Module).
//
bool
SanityCheck::runOnModule(Module & M) {
  //
  // Get a reference to the DSA pass to check.
  //
  dsaPass = &getAnalysis<EQTDDataStructures>();

  //
  // Scan through all instructions in the module and sanity check the load
  // instructions.
  //
  for (Module::iterator F = M.begin(); F != M.end(); ++F) {
    for (Function::iterator BB = F->begin(); BB != F->end(); ++BB) {
      for (BasicBlock::iterator I = BB->begin(); I != BB->end(); ++I) {
        if (LoadInst * LI = dyn_cast<LoadInst>(I))
          checkLoad (*LI);
      }
    }
  }

  return false;
}
