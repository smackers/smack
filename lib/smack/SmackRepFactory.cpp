#include "SmackRepFactory.h"

namespace smack {
   
    SmackRep* SmackRepFactory::createSmackRep(llvm::DataLayout *td) {
//        return new SmackRep2dMem(td);
        return new SmackRepFlatMem(td);
    }

} // namespace smack
