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

  rep->setProgram( &program );
  rep->collectRegions(m);
  
  DEBUG(errs() << "Analyzing globals...\n");

  for (llvm::Module::const_global_iterator
       x = m.global_begin(), e = m.global_end(); x != e; ++x)
    program.addDecls(rep->globalDecl(x));
  
  if (rep->hasStaticInits())
    program.addDecl(rep->getStaticInit());

  DEBUG(errs() << "Analyzing functions...\n");

  for (llvm::Module::iterator func = m.begin(), e = m.end();
       func != e; ++func) {

    if (rep->isIgnore(func))
      continue;
    
    if (!func->isVarArg())
      program.addDecls(rep->globalDecl(func));

    ProcDecl* proc = rep->proc(func,0);
    program.addDecl(proc);

    if (!func->isDeclaration() && !func->empty()
        && !func->getEntryBlock().empty()) {

      DEBUG(errs() << "Analyzing function: " << rep->id(func) << "\n");

      map<const llvm::BasicBlock*, Block*> known;
      stack<llvm::BasicBlock*> workStack;
      SmackInstGenerator igen(*rep, (ProcDecl&) *proc, known);

      llvm::BasicBlock& entry = func->getEntryBlock();
      workStack.push(&entry);
      known[&entry] = igen.createBlock();
      
      // First execute static initializers, in the main procedure.
      if (rep->id(func) == "main" && rep->hasStaticInits())
        known[&entry]->addStmt(Stmt::call(SmackRep::STATIC_INIT));

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

      DEBUG(errs() << "Finished analyzing function: " << rep->id(func) << "\n\n");
    }

    // MODIFIES
    // ... to do below, after memory splitting is determined.
  }

  // MODIFIES
  vector<ProcDecl*> procs = program.getProcs();
  for (unsigned i=0; i<procs.size(); i++) {
    
    if (procs[i]->hasBody()) {
      procs[i]->addMods(rep->getModifies());
    
    } else {
      vector< pair<string,string> > rets = procs[i]->getRets();
      for (vector< pair<string,string> >::iterator r = rets.begin();
          r != rets.end(); ++r) {
        
        // TODO should only do this for returned POINTERS.
        // procs[i]->addEnsures(rep->declareIsExternal(Expr::id(r->first)));
      }
    }
  }
  
  // NOTE we must do this after instruction generation, since we would not 
  // otherwise know how many regions to declare.
  program.appendPrelude(rep->getPrelude());
}

} // namespace smack

