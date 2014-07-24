//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/SmackModuleGenerator.h"
#include "smack/SmackOptions.h"
#include "smack/Slicing.h"

namespace smack {

llvm::RegisterPass<SmackModuleGenerator> X("smack", "SMACK generator pass");
char SmackModuleGenerator::ID = 0;

class SpecCollector : public llvm::InstVisitor<SpecCollector> {
private:
  SmackRep& rep;
  ProcDecl& proc;
  Program& program;
  
  vector<const Expr*> slices;

public:
  SpecCollector(SmackRep& r, ProcDecl& d, Program& p)
    : rep(r), proc(d), program(p) {}
  
  vector<const Expr*>& getSlices() {
    return slices;
  }

  Expr* slice_expr(SmackRep& rep, llvm::Value* v) {
    CodeExpr* code = new CodeExpr(*rep.getProgram());
    SmackInstGenerator igen(rep, *code, slices.size());
    llvm::Function* sliced = llvm::get_slice(v);
    igen.setQuantifierMap(&slices);
    igen.visit(sliced);
    delete sliced;
    return code;
  }

  void visitCallInst(llvm::CallInst& ci) {
    using namespace llvm;
    Function* f = ci.getCalledFunction();

    if (f && rep.id(f).find("forall") != string::npos) {
      assert(ci.getNumArgOperands() == 2 && "Unexpected operands to forall.");
      Value* var = ci.getArgOperand(0);
      Value* arg = ci.getArgOperand(1);
      const Expr* e = Expr::forall(rep.getString(var), "int", slice_expr(rep,arg));
      ci.setArgOperand(1,ConstantInt::get(IntegerType::get(ci.getContext(),32),slices.size()));
      slices.push_back(e);
      llvm::remove_slice(arg);

    } else if (f && rep.id(f).find("requires") != string::npos) {
      assert(ci.getNumArgOperands() == 1 && "Unexpected operands to requires.");
      proc.addRequires(slice_expr(rep,ci.getArgOperand(0)));
      llvm::remove_slice(&ci);

    } else if (f && rep.id(f).find("ensures") != string::npos) {
      assert(ci.getNumArgOperands() == 1 && "Unexpected operands to ensures.");
      proc.addEnsures(slice_expr(rep,ci.getArgOperand(0)));
      llvm::remove_slice(&ci);

    } else if (f && rep.id(f).find("invariant") != string::npos) {
      assert(ci.getNumArgOperands() == 1 && "Unexpected operands to invariant.");
      Value* arg = ci.getArgOperand(0);
      const Expr* e = slice_expr(rep,arg);
      ci.setArgOperand(0,ConstantInt::get(IntegerType::get(ci.getContext(),32),slices.size()));
      slices.push_back(e);
      llvm::remove_slice(arg);
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
      igen.setQuantifierMap(&sc.getSlices());
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

