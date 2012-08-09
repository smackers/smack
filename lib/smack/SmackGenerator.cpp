//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "SmackGenerator.h"

using namespace smack;

RegisterPass<SmackGenerator> X("smack", "SMACK generator pass");
char SmackGenerator::ID = 0;

bool SmackGenerator::runOnModule(Module &m) {
  TargetData& targetData = getAnalysis<TargetData>();
  module = new SmackModule();

  DEBUG(errs() << "Analyzing globals...\n");
  for (Module::const_global_iterator g = m.global_begin(), e = m.global_end(); g != e; ++g) {
    if (isa<GlobalVariable>(g)) {
      std::string globalName = translateName(g);
      module->addGlobalVariable(globalName);
    }
  }

  DEBUG(errs() << "Analyzing functions...\n");
  SmackInstVisitor smackVisitor(&targetData);

  for (Module::iterator func = m.begin(), e = m.end(); func != e; ++func) {
    if (func->isDeclaration() || func->getName().str().find("__SMACK") != std::string::npos ) {
      continue;
    }
    DEBUG(errs() << "Analyzing function: " << func->getName().str() << "\n");

    Procedure* procedure = new Procedure(func->getName().str());

    // set return variable name
    if (func->getReturnType()->getTypeID() != Type::VoidTyID) {
      procedure->setNotVoid();
      std::string returnVarName = "__SMACK_";
      returnVarName.append(func->getName().str());
      returnVarName.append("_return");
      procedure->setReturnVar(new VarExpr(translateName(returnVarName)));
    }

    // add arguments
    for (Function::const_arg_iterator i = func->arg_begin(), e = func->arg_end(); i != e; ++i) {
      procedure->addArgument(translateName(i));
    }

    module->addProcedure(procedure);

    std::map<const BasicBlock*, Block*> processedBlocks;
    std::vector<BasicBlock*> workStack;
    std::vector<Block*> smackWorkStack;

    BasicBlock& entryBlock = func->getEntryBlock();
    Block* smackEntryBlock = new Block(&entryBlock);
    procedure->setEntryBlock(smackEntryBlock);

    workStack.push_back(&entryBlock);
    smackWorkStack.push_back(smackEntryBlock);

    while (!workStack.empty()) {
      BasicBlock* basicBlock = workStack.back();
      workStack.pop_back();
      Block* smackBlock = smackWorkStack.back();
      smackWorkStack.pop_back();
      
      if (processedBlocks.count(basicBlock) == 0) {
        processedBlocks[basicBlock] = smackBlock;
        procedure->addBlock(smackBlock);
        smackVisitor.setBlock(smackBlock);
        smackVisitor.visit(basicBlock);
        
        for (succ_iterator i = succ_begin(basicBlock), e = succ_end(basicBlock); i != e; ++i) {
          BasicBlock* succ = *i;
          Block* smackSucc;
          if (processedBlocks.count(succ) == 0) {
            smackSucc = new Block(succ);
            workStack.push_back(succ);
            smackWorkStack.push_back(smackSucc);
          } else {
            assert(processedBlocks.count(succ) == 1);
            smackSucc = processedBlocks[succ];
          }
          smackVisitor.addSuccBlock(smackSucc);
        }
      } else {
        assert(processedBlocks.count(basicBlock) == 1);
      }
    }

    DEBUG(errs() << "Finished analyzing function: " << func->getName().str() << "\n\n");
  }
  return false;
}
