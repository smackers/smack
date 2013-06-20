#include "SmackRepFlatMem.h"

namespace smack {

    const string SmackRepFlatMem::CURRADDR = "$CurrAddr";
//    const string SmackRepFlatMem::PTR_TYPE = "int";

//    const Expr *SmackRepFlatMem::ZERO = Expr::lit(0);
    
    void SmackRepFlatMem::declareGlobals(llvm::Module &m, Program* program) {
      vector<string> globals;
      for (llvm::Module::const_global_iterator
          x = m.global_begin(), e = m.global_end(); x != e; ++x) {

          string name = id(x);
          globals.push_back(name);
          program->addDecl(new ConstDecl(name, SmackRep::PTR_TYPE, true));
//            program->addDecl(new AxiomDecl(
//                Expr::fn(SmackRep::STATIC, rep.obj(Expr::id(name))) ));
      }

      // TODO: size of globals is currently hard-coded to 1024
      if (!globals.empty()) {
          for (unsigned i=0; i<globals.size()-1; i++)
              program->addDecl(new AxiomDecl(
                  Expr::fn("$slt", Expr::fn(SmackRep::ADD, Expr::id(globals[i]), Expr::lit(1024)),
                  Expr::id(globals[i+1]))));
          program->addDecl(new AxiomDecl(
              Expr::fn("$slt", Expr::fn(SmackRep::ADD, Expr::id(globals[globals.size()-1]), Expr::lit(1024)),
              Expr::lit(0))));
      }
    }
    
} // namespace smack
