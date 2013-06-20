#include "SmackRepFactory.h"

namespace smack {
   
    SmackRep* SmackRepFactory::createSmackRep(llvm::DataLayout *td) {
        return new SmackRep2dMem(td);
    }

} // namespace smack
