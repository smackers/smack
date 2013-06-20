#ifndef SMACKREPFACTORY_H
#define SMACKREPFACTORY_H

#include "SmackRep2dMem.h"
#include "SmackRepFlatMem.h"
#include "llvm/DataLayout.h"

namespace smack {
 
    class SmackRepFactory {
    public:
        static SmackRep* createSmackRep(llvm::DataLayout *td);
    };
}

#endif // SMACKREPFACTORY_H
