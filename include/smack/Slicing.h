
#include "llvm/InstVisitor.h"

namespace llvm {
  Function* slice(Value* v, bool exclude=false, bool inPlace=false);
}
