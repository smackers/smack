
#include "llvm/InstVisitor.h"

namespace llvm {
  Function* slice(Value* v, bool exclude=false, bool inPlace=false);
  Function* get_slice(Value* v);
  void remove_slice(Value* v);
}
