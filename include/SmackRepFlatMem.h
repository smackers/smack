#ifndef SMACKREPFLATMEM_H
#define SMACKREPFLATMEM_H

#include "SmackRep.h"

namespace smack {

    using llvm::Regex;
    using llvm::SmallVector;
    using llvm::StringRef;
    using namespace std;

    class SmackRepFlatMem : public SmackRep {
    public:
        static const string CURRADDR;
        static const string PTR_TYPE;
        static const string PRELUDE;

    public:
        SmackRepFlatMem(llvm::DataLayout *td) : SmackRep(td) {}
        void declareGlobals(llvm::Module &m, Program* program);
        void addModifies(Procedure *proc);
        string getPtrType();
        string getPrelude();
    };
}

#endif // SMACKREPFLATMEM_H
