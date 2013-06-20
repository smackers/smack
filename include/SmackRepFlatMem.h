#ifndef SMACKREPFLATMEM_H
#define SMACKREPFLATMEM_H

#include "SmackRep.h"

namespace smack {

    using llvm::Regex;
    using llvm::SmallVector;
    using llvm::StringRef;
    using namespace std;

    class SmackRepFlatMem : public SmackRep {

        int globalsTop;
        
    public:
        static const string CURRADDR;
        static const string PTR_TYPE;
        static const string PRELUDE;

    public:
        SmackRepFlatMem(llvm::DataLayout *td) : SmackRep(td), globalsTop(0) {}
        virtual vector<const Decl*> globalDecl(const llvm::Value *g);
        virtual vector<string> getModifies();
        virtual string getPtrType();
        virtual string getPrelude();
    };
}

#endif // SMACKREPFLATMEM_H
