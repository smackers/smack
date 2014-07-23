//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/SmackModuleGenerator.h"
#include "smack/SmackOptions.h"

namespace smack {

llvm::RegisterPass<SmackModuleGenerator> X("smack", "SMACK generator pass");
char SmackModuleGenerator::ID = 0;

class SpecCollector : public llvm::InstVisitor<SpecCollector> {
private:
  SmackRep& rep;
  ProcDecl& proc;
  Program& program;
  set<llvm::Instruction*> specs;
  set<llvm::BasicBlock*> blocks;

public:
  SpecCollector(SmackRep& r, ProcDecl& d, Program& p)
    : rep(r), proc(d), program(p) {}
  
  // void slicing???(llvm::CallInst& ci) {
  //   stack<llvm::Instruction*> worklist;
  //   worklist.push(&ci);
  //   while (!worklist.empty()) {
  //     llvm::Instruction* i = worklist.top();
  //     worklist.pop();
  //     specs.insert(i);
  //     // i->removeFromParent();
  //     // blocks.insert(i->getParent());
  //     // i->getParent()->removeFromParent();
  //
  //     if (llvm::PHINode* phi = llvm::dyn_cast<llvm::PHINode>(i)) {
  //       for (llvm::PHINode::block_iterator bb = phi->block_begin(); bb != phi->block_end(); ++bb) {
  //         worklist.push( (*bb)->getTerminator() );
  //       }
  //
  //     } else if (llvm::BranchInst* br = llvm::dyn_cast<llvm::BranchInst>(i)) {
  //       if (br->isConditional()) {
  //         DEBUG(errs() << "GOT COND BR.\n");
  //         // worklist.push( br->getCondition() );
  //       }
  //
  //     } else {
  //       i->removeFromParent();
  //       for (llvm::User::op_iterator ops = i->op_begin(); ops != i->op_end(); ++ops) {
  //         if (llvm::Instruction* ii = llvm::dyn_cast<llvm::Instruction>(ops)) {
  //           worklist.push(ii);
  //         }
  //       }
  //     }
  //   }
  // }

  void visitCallInst(llvm::CallInst& ci) {
    llvm::Function* f = ci.getCalledFunction();
    if (f && rep.id(f).find("requires") != string::npos) {
      CodeExpr* code = new CodeExpr(program);
      SmackInstGenerator igen(rep, *code);
      // TODO visit the slice, not the whole proc!
      igen.visit(ci.getParent()->getParent());
      proc.addRequires(code);
    }
  }

};

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

    if (rep->isMallocOrFree(func)) {
      program.addDecls(rep->globalDecl(func));
      continue;
    }

    if (!func->isVarArg())
      program.addDecls(rep->globalDecl(func));

    ProcDecl* proc = rep->proc(func,0);
    if (proc->getName() != "__SMACK_decls")
      program.addDecl(proc);

    if (!func->isDeclaration() && !func->empty()
        && !func->getEntryBlock().empty()) {

      DEBUG(errs() << "Analyzing function: " << rep->id(func) << "\n");

      SpecCollector sc(*rep, *proc, program);
      sc.visit(func);

      SmackInstGenerator igen(*rep, *proc);
      igen.visit(func);

      // First execute static initializers, in the main procedure.
      if (rep->id(func) == "main" && rep->hasStaticInits())
        proc->insert(Stmt::call(SmackRep::STATIC_INIT));

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

