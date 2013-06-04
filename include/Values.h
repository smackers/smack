#ifndef VALUES_H
#define VALUES_H

#include "BoogieAst.h"
#include "llvm/DataLayout.h"

namespace smack {
    
    // TODO What is the right name for this class ?
    // TODO What is it's fundamental purpose / abstraction ?
    
    class Values {
    private:
        llvm::DataLayout *targetData;

    public:
        Values(llvm::DataLayout *td) : targetData(td) {}
        
        Expr * asLit(llvm::Value *v);
        Expr * asLit(unsigned v);
        string asId(const llvm::Value *v);
        string asFnId(llvm::Value *v);
        Expr * asExpr(llvm::Value *v);
        Expr * gepAsExpr(llvm::Value *p, vector<llvm::Value*> ps,
            vector<llvm::Type*> ts);        
        Expr * asIntExpr(llvm::Value *v);
    
        unsigned storageSize(llvm::Type *t);    
        unsigned fieldOffset(llvm::StructType *t, unsigned fieldNo);
    };
}

#endif // VALUES_H
