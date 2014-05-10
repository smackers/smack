//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/SmackRepFlatMem.h"
#include "smack/SmackOptions.h"

namespace smack {

Regex STRING_CONSTANT("^\\.str[0-9]*$");
  
vector<Decl*> SmackRepFlatMem::globalDecl(const llvm::Value* v) {
  using namespace llvm;
  vector<Decl*> decls;
  vector<const Attr*> ax;
  string name = id(v);
  
  if (const GlobalVariable* g = dyn_cast<const GlobalVariable>(v)) {
    if (g->hasInitializer()) {
      const Constant* init = g->getInitializer();
      unsigned numElems = numElements(init);
      unsigned size;
  
      // NOTE: all global variables have pointer type in LLVM
      if (g->getType()->isPointerTy()) {
        PointerType *t = (PointerType*) g->getType();
    
        // in case we can determine the size of the element type ...
        if (t->getElementType()->isSized())
          size = storageSize(t->getElementType());
    
        // otherwise (e.g. for function declarations), use a default size
        else
          size = 1024;
    
      } else
        size = storageSize(g->getType());

      bottom -= size;

      if (!g->hasName() || !STRING_CONSTANT.match(g->getName().str())) {
        if (numElems > 1)
          ax.push_back(Attr::attr("count",numElems));

        decls.push_back(Decl::axiom(Expr::eq(Expr::id(name),Expr::lit(bottom))));
        addInit(getRegion(g), g, init);

        // Expr::fn("$slt",
        //     Expr::fn(SmackRep::ADD, Expr::id(name), Expr::lit(1024)),
        //     Expr::lit(bottom)) ));
      }
    
    } else {
      decls.push_back(Decl::axiom(declareIsExternal(Expr::id(name))));
    }
  }
  decls.push_back(Decl::constant(name, getPtrType(), ax, true));
  return decls;
}

const Expr* SmackRepFlatMem::declareIsExternal(const Expr* e) {
  return Expr::fn("$isExternal",e);
}

string SmackRepFlatMem::getPtrType() {
  return "int";
}

string SmackRepFlatMem::memoryModel() {
  stringstream s;
  s << "axiom $GLOBALS_BOTTOM == " << bottom << ";" << endl;
  return s.str();
}

string SmackRepFlatMem::memcpyProc(int dstReg, int srcReg) {
  stringstream s;

  if (SmackOptions::MemoryModelImpls) {
    s << "procedure $memcpy." << dstReg << "." << srcReg;
    s << "(dest: int, src: int, len: int, align: int, isvolatile: bool)" << endl;
    s << "modifies " << memReg(dstReg) << ";" << endl;
    s << "{" << endl;
    s << "  var $oldSrc: [" << getPtrType() << "] " << getPtrType() << ";" << endl;
    s << "  var $oldDst: [" << getPtrType() << "] " << getPtrType() << ";" << endl;
    s << "  $oldSrc := " << memReg(srcReg) << ";" << endl;
    s << "  $oldDst := " << memReg(dstReg) << ";" << endl;
    s << "  havoc " << memReg(dstReg) << ";" << endl;
    s << "  assume (forall x:int :: dest <= x && x < dest + len ==> " 
      << memReg(dstReg) << "[x] == $oldSrc[src - dest + x]);" << endl;
    s << "  assume (forall x:int :: !(dest <= x && x < dest + len) ==> "
      << memReg(dstReg) << "[x] == $oldDst[x]);" << endl;
    s << "}" << endl;
  } else {
    s << "procedure $memcpy." << dstReg << "." << srcReg;
    s << "(dest: int, src: int, len: int, align: int, isvolatile: bool);" << endl;
    s << "modifies " << memReg(dstReg) << ";" << endl;
    s << "ensures (forall x:int :: dest <= x && x < dest + len ==> " 
      << memReg(dstReg) << "[x] == old(" << memReg(srcReg) << ")[src - dest + x]);" 
      << endl;
    s << "ensures (forall x:int :: !(dest <= x && x < dest + len) ==> "
      << memReg(dstReg) << "[x] == old(" << memReg(dstReg) << ")[x]);" << endl;
  }

  return s.str();
}

string SmackRepFlatMem::memsetProc(int dstReg) {
  stringstream s;

  if (SmackOptions::MemoryModelImpls) {
    s << "procedure $memset." << dstReg;
    s << "(dest: int, val: int, len: int, align: int, isvolatile: bool)" << endl;
    s << "modifies " << memReg(dstReg) << ";" << endl;
    s << "{" << endl;
    s << "  var $oldDst: [" << getPtrType() << "] " << getPtrType() << ";" << endl;
    s << "  $oldDst := " << memReg(dstReg) << ";" << endl;
    s << "  havoc " << memReg(dstReg) << ";" << endl;
    s << "  assume (forall x:int :: dest <= x && x < dest + len ==> "
      << memReg(dstReg) << "[x] == val);" << endl;
    s << "  assume (forall x:int :: !(dest <= x && x < dest + len) ==> "
      << memReg(dstReg) << "[x] == $oldDst[x]);" << endl;
    s << "}" << endl;
  } else {
    s << "procedure $memset." << dstReg;
    s << "(dest: int, val: int, len: int, align: int, isvolatile: bool);" << endl;
    s << "modifies " << memReg(dstReg) << ";" << endl;
    s << "ensures (forall x:int :: dest <= x && x < dest + len ==> "
      << memReg(dstReg) << "[x] == val);"
      << endl;
    s << "ensures (forall x:int :: !(dest <= x && x < dest + len) ==> "
      << memReg(dstReg) << "[x] == old(" << memReg(dstReg) << ")[x]);" << endl;
  }

  return s.str();
}

} // namespace smack
