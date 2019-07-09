//
// This file is distributed under the MIT License. See LICENSE for details.
//
#define DEBUG_TYPE "smack-mod-gen"
#include "smack/SmackModuleGenerator.h"
#include "smack/BoogieAst.h"
#include "smack/Debug.h"
#include "smack/Naming.h"
#include "smack/Prelude.h"
#include "smack/Regions.h"
#include "smack/SmackInstGenerator.h"
#include "smack/SmackOptions.h"
#include "smack/SmackRep.h"

namespace smack {

llvm::RegisterPass<SmackModuleGenerator> X("smack", "SMACK generator pass");
char SmackModuleGenerator::ID = 0;

SmackModuleGenerator::SmackModuleGenerator() : ModulePass(ID) {
  program = new Program();
}

void SmackModuleGenerator::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<llvm::LoopInfoWrapperPass>();
  AU.addRequired<Regions>();
}

bool SmackModuleGenerator::runOnModule(llvm::Module &m) {
  generateProgram(m);
  return false;
}

void SmackModuleGenerator::generateProgram(llvm::Module &M) {

  Naming naming;
  SmackRep rep(&M.getDataLayout(), &naming, program, &getAnalysis<Regions>());
  std::list<Decl *> &decls = program->getDeclarations();

  SDEBUG(errs() << "Analyzing globals...\n");

  for (auto &G : M.globals()) {
    auto ds = rep.globalDecl(&G);
    decls.insert(decls.end(), ds.begin(), ds.end());
  }

  SDEBUG(errs() << "Analyzing functions...\n");

  for (auto &F : M) {

    // Reset the counters for per-function names
    naming.reset();

    SDEBUG(errs() << "Analyzing function: " << naming.get(F) << "\n");

    auto ds = rep.globalDecl(&F);
    decls.insert(decls.end(), ds.begin(), ds.end());

    auto procs = rep.procedure(&F);
    assert(procs.size() > 0);

    if (naming.get(F) != Naming::DECLARATIONS_PROC)
      decls.insert(decls.end(), procs.begin(), procs.end());

    if (F.isDeclaration())
      continue;

    if (!F.empty() && !F.getEntryBlock().empty()) {
      SDEBUG(errs() << "Analyzing function body: " << naming.get(F) << "\n");

      for (auto P : procs) {
        SmackInstGenerator igen(
            getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo(), &rep, P,
            &naming);
        SDEBUG(errs() << "Generating body for " << naming.get(F) << "\n");
        igen.visit(F);
        SDEBUG(errs() << "\n");

        // First execute static initializers, in the main procedure.
        if (F.hasName() && SmackOptions::isEntryPoint(F.getName())) {
          P->insert(Stmt::call(Naming::INITIALIZE_PROC));

        } else if (naming.get(F).find(Naming::INIT_FUNC_PREFIX) == 0)
          rep.addInitFunc(&F);
      }
      SDEBUG(errs() << "Finished analyzing function: " << naming.get(F)
                    << "\n\n");
    }

    // MODIFIES
    // ... to do below, after memory splitting is determined.
  }

  auto ds = rep.auxiliaryDeclarations();
  decls.insert(decls.end(), ds.begin(), ds.end());
  decls.insert(decls.end(), rep.getInitFuncs());

  // NOTE we must do this after instruction generation, since we would not
  // otherwise know how many regions to declare.
  Prelude prelude(rep);
  program->appendPrelude(prelude.getPrelude());

  std::list<Decl *> kill_list;
  for (auto D : *program) {
    if (auto P = dyn_cast<ProcDecl>(D)) {
      if (rep.isContractExpr(D->getName())) {
        decls.insert(decls.end(), Decl::code(P));
        kill_list.push_back(P);
      }
    }
  }
  for (auto D : kill_list)
    decls.erase(std::remove(decls.begin(), decls.end(), D), decls.end());
}

} // namespace smack
