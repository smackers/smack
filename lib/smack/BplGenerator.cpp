//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "BplGenerator.h"

using namespace smack;

RegisterPass<BplGenerator> X("bpl", "BoogiePL generator pass");
char BplGenerator::ID = 0;

bool BplGenerator::runOnModule(Module &m) {
  TargetData& targetData = getAnalysis<TargetData>();
  bplModule = new BPLModule();

  DEBUG(errs() << "Analyzing globals...\n");
  for (Module::const_global_iterator g = m.global_begin(), e = m.global_end(); g != e; ++g) {
    if (isa<GlobalVariable>(g)) {
      std::string globalName = translateName(g);
      bplModule->addGlobalVariable(globalName);
    }
  }

  DEBUG(errs() << "Analyzing functions...\n");
  BPLInstVisitor bplVisitor(&targetData);

  for (Module::iterator func = m.begin(), e = m.end(); func != e; ++func) {
    if (func->isDeclaration() || func->getName().str().find("__SMACK") != std::string::npos ) {
      continue;
    }
    DEBUG(errs() << "Analyzing function: " << func->getName().str() << "\n");

    BPLProcedure* bplProc = new BPLProcedure(func->getName().str());

    // set return variable name
    if (func->getReturnType()->getTypeID() != Type::VoidTyID) {
      bplProc->setNotVoid();
      std::string returnVarName = "__SMACK_";
      returnVarName.append(func->getName().str());
      returnVarName.append("_return");
      bplProc->setReturnVar(new BPLVarExpr(translateName(returnVarName)));
    }

    // add arguments
    for (Function::const_arg_iterator i = func->arg_begin(), e = func->arg_end(); i != e; ++i) {
      bplProc->addArgument(translateName(i));
    }

    bplModule->addProcedure(bplProc);

    std::map<const BasicBlock*, BPLBlock*> processedBlocks;
    std::vector<BasicBlock*> workStack;
    std::vector<BPLBlock*> bplWorkStack;

    BasicBlock& entryBlock = func->getEntryBlock();
    BPLBlock* bplEntryBlock = new BPLBlock(&entryBlock);
    bplProc->setEntryBlock(bplEntryBlock);

    workStack.push_back(&entryBlock);
    bplWorkStack.push_back(bplEntryBlock);

    while (!workStack.empty()) {
      BasicBlock* block = workStack.back();
      workStack.pop_back();
      BPLBlock* bplBlock = bplWorkStack.back();
      bplWorkStack.pop_back();
      
      if (processedBlocks.count(block) == 0) {
        processedBlocks[block] = bplBlock;
        bplProc->addBlock(bplBlock);
        bplVisitor.setBPLBlock(bplBlock);
        bplVisitor.visit(block);
        
        for (succ_iterator i = succ_begin(block), e = succ_end(block); i != e; ++i) {
          BasicBlock* succ = *i;
          BPLBlock* bplSucc;
          if (processedBlocks.count(succ) == 0) {
            bplSucc = new BPLBlock(succ);
            workStack.push_back(succ);
            bplWorkStack.push_back(bplSucc);
          } else {
            assert(processedBlocks.count(succ) == 1);
            bplSucc = processedBlocks[succ];
          }
          bplVisitor.addSuccBlock(bplSucc);
        }
      } else {
        assert(processedBlocks.count(block) == 1);
      }
    }

    DEBUG(errs() << "Finished analyzing function: " << func->getName().str() << "\n\n");
  }
  return false;
}
