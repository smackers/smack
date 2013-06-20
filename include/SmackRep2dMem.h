#ifndef SMACKREP2DMEM_H
#define SMACKREP2DMEM_H

#include "SmackRep.h"

namespace smack {

    using llvm::Regex;
    using llvm::SmallVector;
    using llvm::StringRef;
    using namespace std;

    class SmackRep2dMem : public SmackRep {
    public:
        static const string PTR_TYPE;
        static const string REF_TYPE;
        static const string PRELUDE;

    public:
        SmackRep2dMem(llvm::DataLayout *td) : SmackRep(td) {}
        void declareGlobals(llvm::Module &m, Program* program);
        void addModifies(Procedure *proc);
        string getPtrType();
        string getPrelude();
    };
}

#endif // SMACKREP2DMEM_H
