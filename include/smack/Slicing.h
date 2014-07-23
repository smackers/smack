
#include "llvm/InstVisitor.h"

namespace llvm {
  Function* slice(Function* f, Value* v, bool keep=false);
}

namespace smack {  
  Expr* slice(SmackRep& rep, llvm::Value* v, bool keep=false);
}
