#ifndef VALUES_H
#define VALUES_H

#include "BoogieAst.h"
#include "llvm/DataLayout.h"
#include "llvm/InstrTypes.h"

namespace smack {
    
    class SmackRep {
    public:
        static const string MEMORY;
        static const string ALLOC;
        static const string BLOCK_LBL;
        static const string RET_VAR;
        static const string BOOL_VAR;
        static const string PTR_VAR;
        static const string BOOL_TYPE;
        static const string PTR_TYPE;
        static const string REF_TYPE;
        static const string NULL_VAL;
        static const string UNDEF_VAL;

        static const string ALLOCA;
        static const string MALLOC;
        static const string FREE;

        static const string PTR;
        static const string STATIC;
        static const string OBJ;
        static const string OFF;
        static const string PA;
    
        static const string B2P;
        static const string I2P;
        static const string P2I;
        static const string I2B;
        static const string B2I;
        
        static const string ADD;
        static const string SUB;
        static const string MUL;
        static const string SDIV;
        static const string UDIV;
        static const string SREM;
        static const string UREM;
        static const string AND;
        static const string OR;
        static const string XOR;
        static const string LSHR;
        static const string ASHR;
        static const string SHL;
        
        static const string SGE;
        static const string UGE;
        static const string SLE;
        static const string ULE;
        static const string SLT;
        static const string ULT;
        static const string SGT;
        static const string UGT;
        
        static const Expr *NUL;
        static const Expr *UNDEF;
        static const Expr *ZERO;
        
    private:
        llvm::DataLayout *targetData;

    public:
        SmackRep(llvm::DataLayout *td) : targetData(td) {}

        bool isSmackName(string n);
        bool isBool(llvm::Type *t);
        bool isBool(llvm::Value *v);
        string type(llvm::Type *t);
        string type(llvm::Value *v);
        
        unsigned storageSize(llvm::Type *t);    
        unsigned fieldOffset(llvm::StructType *t, unsigned fieldNo);
        
        const Expr * mem(const Expr *e);
        const Expr * ptr(const Expr *obj, const Expr *off);
        const Expr * obj(const Expr *e);
        const Expr * off(const Expr *e);
        const Expr * i2p(const Expr *e);
        const Expr * p2i(const Expr *e);
        const Expr * b2p(const Expr *e);
        const Expr * i2b(const Expr *e);
        const Expr * b2i(const Expr *e);
        
        const Expr * pa(const Expr *e, int x, int y);
        const Expr * pa(const Expr *e, const Expr *x, int y);
        const Expr * pa(const Expr *e, const Expr *x, const Expr *y);

        string id(const llvm::Value *v);
        const Expr * lit(llvm::Value *v);
        const Expr * lit(unsigned v);
        const Expr * ptrArith(llvm::Value *p, vector<llvm::Value*> ps,
            vector<llvm::Type*> ts);
        const Expr * expr(llvm::Value *v);
        const Expr * op(llvm::BinaryOperator& o);
        const Expr * pred(llvm::CmpInst& ci);        
    };
}

#endif // VALUES_H
