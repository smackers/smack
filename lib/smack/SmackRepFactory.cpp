#include "SmackRepFactory.h"

namespace smack {
   
    SmackRep SmackRepFactory::createSmackRep(llvm::DataLayout *td) {
        return SmackRepFlatMem(td);
    }

} // namespace smack
