#ifndef SMACKREPFACTORY_H
#define SMACKREPFACTORY_H

#include "SmackRep2dMem.h"
#include "SmackRepFlatMem.h"
#include "llvm/DataLayout.h"

namespace smack {
 
    enum MemMod {
        flat, twodim
    };

    class SmackRepFactory {
    public:
        static SmackRep* createSmackRep(llvm::DataLayout *td, MemMod memoryModel);
    };
}

#endif // SMACKREPFACTORY_H
