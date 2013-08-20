//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/SmackModuleGenerator.h"
#include "smack/SmackOptions.h"

namespace smack {

llvm::RegisterPass<SmackModuleGenerator> X("smack", "SMACK generator pass");
char SmackModuleGenerator::ID = 0;

void SmackModuleGenerator::generateProgram(llvm::Module& m, SmackRep* rep) {

  program = new Program("");

  DEBUG(errs() << "Analyzing globals...\n");

  for (llvm::Module::const_global_iterator
       x = m.global_begin(), e = m.global_end(); x != e; ++x)
    program->addDecls(rep->globalDecl(x));

  DEBUG(errs() << "Analyzing functions...\n");

  set<pair<llvm::Function*, int> > missingDecls;
  set<string> moreDecls;

  for (llvm::Module::iterator func = m.begin(), e = m.end();
       func != e; ++func) {

    string name = rep->id(func);

    if (rep->isSmackName(name) || rep->isProcIgnore(name))
      continue;

    program->addDecls(rep->globalDecl(func));

    if (func->isDeclaration())
      continue;

    DEBUG(errs() << "Analyzing function: " << name << "\n");

    Procedure* proc = new Procedure(name);
    program->addProc(proc);

    // BODY
    if (!func->isDeclaration() && !func->empty()
        && !func->getEntryBlock().empty()) {

      map<const llvm::BasicBlock*, Block*> known;
      stack<llvm::BasicBlock*> workStack;
      SmackInstGenerator igen(rep, *proc, known, missingDecls, moreDecls);

      llvm::BasicBlock& entry = func->getEntryBlock();
      workStack.push(&entry);
      known[&entry] = igen.createBlock();

      // INVARIANT: knownBlocks.CONTAINS(b) iff workStack.CONTAINS(b)
      // or workStack.CONTAINED(b) at some point in time.
      while (!workStack.empty()) {
        llvm::BasicBlock* b = workStack.top();
        workStack.pop();

        for (llvm::succ_iterator s = succ_begin(b),
             e = succ_end(b); s != e; ++s) {

          // uncovered basic block
          if (known.count(*s) == 0) {
            known[*s] = igen.createBlock();
            workStack.push(*s);
          }
        }

        // NOTE: here we are sure that all successor blocks have
        // already been created, and are mapped for the visitor.

        igen.setCurrBlock(known[b]);
        igen.visit(b);
      }
    }

    // PARAMETERS
    for (llvm::Function::const_arg_iterator
         arg = func->arg_begin(), e = func->arg_end(); arg != e; ++arg) {
      proc->addParam(rep->id(arg), rep->type(arg->getType()));
    }

    // RETURNS
    if (! func->getReturnType()->isVoidTy())
      proc->addRet(SmackRep::RET_VAR, rep->type(func->getReturnType()));

    // MODIFIES
    // ... to do below, after memory splitting is determined.

    DEBUG(errs() << "Finished analyzing function: " << name << "\n\n");
  }

  // Add any missing procedure declarations
  // NOTE: for the moment, these correspond to VARARG procedures.
  for (set<pair<llvm::Function*, int> >::iterator d = missingDecls.begin();
       d != missingDecls.end(); ++d) {
    llvm::Function* func = d->first;
    int numArgs = d->second;

    stringstream name;
    name << rep->id(func);
    if (func->isVarArg() && numArgs > 0) {
      name << "#" << numArgs;
    }

    Procedure* p = new Procedure(name.str());

    if (func->isVarArg()) {
      for (int i = 0; i < numArgs; i++) {
        stringstream param;
        param << "p" << i;
        p->addParam(param.str(), rep->getPtrType());
      }
    } else {
      int i = 0;
      for (llvm::Function::const_arg_iterator
           arg = func->arg_begin(), e = func->arg_end(); arg != e; ++arg, ++i) {
        stringstream param;
        param << "p" << i;
        p->addParam(param.str(), rep->type(arg->getType()));
      }
    }

    if (! func->getReturnType()->isVoidTy())
      p->addRet(SmackRep::RET_VAR, rep->getPtrType());
    program->addProc(p);
  }

  // MODIFIES
  for ( vector<Procedure*>::const_iterator p = program->pbegin();
        p != program->pend(); ++p ) {
    (*p)->addMods(rep->getModifies());
  }

  for (set<string>::iterator d = moreDecls.begin();
       d != moreDecls.end(); ++d) {
     program->appendPrelude(*d);
   }
  
  // NOTE we must do this after instruction generation, since we would not 
  // otherwise know how many regions to declare.
  program->appendPrelude(rep->getPrelude());
}

} // namespace smack

