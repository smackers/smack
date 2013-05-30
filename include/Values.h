#ifndef VALUES_H
#define VALUES_H

#include "BoogieAst.h"
#include "llvm/DataLayout.h"

namespace smack {
    class Values {
    private:
        llvm::DataLayout *targetData;
    public:
        Values(llvm::DataLayout *td) : targetData(td) {}
        
        Expr * lit(llvm::Value *v);
        Expr * lit(unsigned v);
        string id(const llvm::Value *v);
        string fun(llvm::Value *v);
        Expr * expr(llvm::Value *v);
        
        Expr * integer(llvm::Value *v);
    
        unsigned storageSize(llvm::Type *t);    
        unsigned fieldOffset(llvm::StructType *t, unsigned fieldNo);
    };
}

#endif // VALUES_H
