//
// This file is distributed under the MIT License. See LICENSE for details.
//
#define DEBUG_TYPE "smack-mod-gen"
#include "smack/SmackModuleGenerator.h"
#include "smack/SmackOptions.h"
#include "smack/Contracts.h"

namespace smack {

llvm::RegisterPass<SmackModuleGenerator> X("smack", "SMACK generator pass");
char SmackModuleGenerator::ID = 0;

void SmackModuleGenerator::generateProgram(llvm::Module& m) {

  Naming naming;
  SmackRep rep(m.getDataLayout(), naming, program, getAnalysis<Regions>());

  DEBUG(errs() << "Analyzing globals...\n");

  for (llvm::Module::const_global_iterator
       x = m.global_begin(), e = m.global_end(); x != e; ++x)
    program.addDecls(rep.globalDecl(x));

  DEBUG(errs() << "Analyzing functions...\n");

  for (llvm::Module::iterator func = m.begin(), e = m.end();
       func != e; ++func) {

    // Reset the counters for per-function names
    naming.reset();

    DEBUG(errs() << "Analyzing function: " << naming.get(*func) << "\n");

    // TODO: Implement function pointers of vararg functions properly
    // if (!func->isVarArg())
    program.addDecls(rep.globalDecl(func));

    // TODO this will cover the cases of malloc, memcpy, memset, …
    if (func->isDeclaration()) {
      program.addDecls(rep.decl(func));
      continue;
    }

    vector<ProcDecl*> procs = rep.proc(func);
    assert(procs.size() > 0);
    if (procs[0]->getName() != Naming::DECLARATIONS_PROC)
      program.addDecls(procs);

    if (!func->empty() && !func->getEntryBlock().empty()) {

      DEBUG(errs() << "Analyzing function body: " << naming.get(*func) << "\n");

      for (vector<ProcDecl*>::iterator proc = procs.begin(); proc != procs.end(); ++proc) {
        Slices slices;
        ContractsExtractor ce(rep, **proc, naming, slices);
        SmackInstGenerator igen(rep, **proc, naming, slices);

        DEBUG(errs() << "Extracting contracts for " << naming.get(*func) << " from ");
        DEBUG(errs() << *func << "\n");
        ce.visit(func);
        DEBUG(errs() << "\n");

        DEBUG(errs() << "Generating body for " << naming.get(*func) << " from ");
        DEBUG(errs() << *func << "\n");
        igen.visit(func);
        DEBUG(errs() << "\n");

        // First execute static initializers, in the main procedure.
        if (func->hasName() && SmackOptions::isEntryPoint(func->getName())) {
          (*proc)->insert(Stmt::call(Naming::INITIALIZE_PROC));

        } else if (naming.get(*func).find(Naming::INIT_FUNC_PREFIX) == 0)
          rep.addInitFunc(func);
      }
      DEBUG(errs() << "Finished analyzing function: " << naming.get(*func) << "\n\n");
    }

    // MODIFIES
    // ... to do below, after memory splitting is determined.
  }

  program.addDecl(rep.getInitFuncs());

  // MODIFIES
  vector<ProcDecl*> procs = program.getProcs();
  for (unsigned i=0; i<procs.size(); i++) {

    if (procs[i]->hasBody()) {
      procs[i]->addMods(rep.getModifies());

    } else {
      vector< pair<string,string> > rets = procs[i]->getRets();
      for (vector< pair<string,string> >::iterator r = rets.begin();
          r != rets.end(); ++r) {

        // TODO should only do this for returned POINTERS.
        // procs[i]->addEnsures(rep.declareIsExternal(Expr::id(r->first)));
      }
    }
  }

  // NOTE we must do this after instruction generation, since we would not
  // otherwise know how many regions to declare.
  program.appendPrelude(rep.getPrelude());
}

} // namespace smack
