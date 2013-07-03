#include "SmackRepFactory.h"

namespace smack {

SmackRep* SmackRepFactory::createSmackRep(llvm::DataLayout* td, MemMod memoryModel) {
  if (memoryModel == twodim) {
    return new SmackRep2dMem(td);
  } else {
    return new SmackRepFlatMem(td);
  }
}

} // namespace smack
