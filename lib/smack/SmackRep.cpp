#include "SmackRep.h"

namespace smack {
   
    const string SmackRep::MEMORY = "$Mem";
    const string SmackRep::ALLOC = "$Alloc";
    const string SmackRep::BLOCK_LBL = "$bb";
    const string SmackRep::RET_VAR = "$r";
    const string SmackRep::BOOL_VAR = "$b";
    const string SmackRep::PTR_VAR = "$p";
    const string SmackRep::BOOL_TYPE = "bool";
    const string SmackRep::PTR_TYPE = "int";
    const string SmackRep::NULL_VAL = "$NULL";
    const string SmackRep::UNDEF_VAL = "$UNDEF";

    const string SmackRep::ALLOCA = "$alloca";
    const string SmackRep::MALLOC = "$malloc";
    const string SmackRep::FREE = "$free";

    const string SmackRep::PTR = "$ptr";
    const string SmackRep::STATIC = "$static";
    const string SmackRep::OBJ = "$obj";
    const string SmackRep::OFF = "$off";
    const string SmackRep::PA = "$pa";

    const string SmackRep::B2P = "$b2p";
    const string SmackRep::I2P = "$i2p";
    const string SmackRep::P2I = "$p2i";
    const string SmackRep::I2B = "$i2b";
    const string SmackRep::B2I = "$b2i";
    
    const string SmackRep::ADD = "$add";
    const string SmackRep::SUB = "$sub";
    const string SmackRep::MUL = "$mul";
    const string SmackRep::SDIV = "$sdiv";
    const string SmackRep::UDIV = "$udiv";
    const string SmackRep::SREM = "$srem";
    const string SmackRep::UREM = "$urem";
    const string SmackRep::AND = "$and";
    const string SmackRep::OR = "$or";
    const string SmackRep::XOR = "$xor";
    const string SmackRep::LSHR = "$lshr";
    const string SmackRep::ASHR = "$ashr";
    const string SmackRep::SHL = "$shl";
    
    const string SmackRep::SGE = "$sge";
    const string SmackRep::UGE = "$uge";
    const string SmackRep::SLE = "$sle";
    const string SmackRep::ULE = "$ule";
    const string SmackRep::SLT = "$slt";
    const string SmackRep::ULT = "$ult";
    const string SmackRep::SGT = "$sgt";
    const string SmackRep::UGT = "$ugt";
    
    const Expr *SmackRep::NUL = Expr::id(NULL_VAL);
    const Expr *SmackRep::UNDEF = Expr::id(UNDEF_VAL);
    
    const Expr *SmackRep::ZERO = Expr::lit(0);
    
    const int SmackRep::width = 0;

    // TODO Do the following functions belong here ?

    string EscapeString(string str) {
      str = llvm::DOT::EscapeString(str);
      return str;
    }

    Regex BPL_KW(
      "^(bool|int|false|true|old|forall|exists|requires|modifies|ensures|invariant"
      "|unique|finite|complete|type|const|function|axiom|var|procedure"
      "|implementation|where|returns|assume|assert|havoc|call|return|while"
      "|break|goto|if|else|div)$" );
    Regex SMACK_NAME(".*__SMACK_.*");
    Regex SMACK_ASSERT(".*__SMACK_assert.*");
    Regex SMACK_ASSUME(".*__SMACK_assume.*");
    Regex SMACK_REC_OBJ(".*__SMACK_record_obj.*");
    Regex SMACK_REC_INT(".*__SMACK_record_int.*");
    Regex SMACK_REC_PTR(".*__SMACK_record_ptr.*");

    bool isBplKeyword(string s) {
      return BPL_KW.match(s);
    }
        
    bool SmackRep::isSmackName(string n) {
        return SMACK_NAME.match(n);
    }
    
    bool SmackRep::isSmackAssert(llvm::Function *f) {
        return SMACK_ASSERT.match(id(f));
    }
    
    bool SmackRep::isSmackAssume(llvm::Function *f) {
        return SMACK_ASSUME.match(id(f));
    }
    
    bool SmackRep::isSmackRecObj(llvm::Function *f) {
        return SMACK_REC_OBJ.match(id(f));
    }
    
    bool SmackRep::isSmackRecInt(llvm::Function *f) {
        return SMACK_REC_INT.match(id(f));
    }
    
    bool SmackRep::isSmackRecPtr(llvm::Function *f) {
        return SMACK_REC_PTR.match(id(f));
    }
    
    bool SmackRep::isBool(llvm::Type *t) {
        return t->isIntegerTy(1);
    }
    
    bool SmackRep::isBool(llvm::Value *v) {
        return isBool(v->getType());
    }    
    
    string SmackRep::type(llvm::Type *t) {
        return isBool(t) ? BOOL_TYPE : PTR_TYPE;
    }
    
    string SmackRep::type(llvm::Value *v) {
        return type(v->getType());
    }    
        
    unsigned SmackRep::storageSize(llvm::Type *t) {
        return targetData->getTypeStoreSize(t);
    }
    
    unsigned SmackRep::fieldOffset(llvm::StructType *t, unsigned fieldNo) {
        return targetData->getStructLayout(t)->getElementOffset(fieldNo);
    }

    // NOTE: flexibility for future alternative memory models
    const Expr * SmackRep::mem(const Expr *e) {
        return Expr::sel(Expr::id(SmackRep::MEMORY), e);
    }
    
    const Expr * SmackRep::ptr(const Expr *obj, const Expr *off) {
        return Expr::fn(PTR, obj, off);
    }
    
    const Expr * SmackRep::obj(const Expr *e) {
        return Expr::fn(OBJ,e);
    }
    
    const Expr * SmackRep::off(const Expr *e) {
        return Expr::fn(OFF,e);
    }
    
    const Expr * SmackRep::i2p(const Expr *e) {
        return Expr::fn(I2P, e);
    }
    
    const Expr * SmackRep::p2i(const Expr *e) {
        return Expr::fn(P2I, e);
    }
    
    const Expr * SmackRep::b2p(const Expr *e) {
        return Expr::fn(B2P, e);
    }
    
    const Expr * SmackRep::i2b(const Expr *e) {
        return Expr::fn(I2B, e);
    }
    
    const Expr * SmackRep::b2i(const Expr *e) {
        return Expr::fn(B2I, e);
    }
    
    const Expr * SmackRep::pa(const Expr *e, int x, int y) {
        return pa(e, Expr::lit(x), Expr::lit(y));
    }
    
    const Expr * SmackRep::pa(const Expr *e, const Expr *x, int y) {
        return pa(e, x, Expr::lit(y));
    }
    
    const Expr * SmackRep::pa(const Expr *e, const Expr *x, const Expr *y) {
        return Expr::fn(PA, e, x, y);
    }
            
    string SmackRep::id(const llvm::Value *v) {
        string name;
    
        if (v->hasName()) {
            name = v->getName().str();
            
        } else {
            assert(false && "expected named value.");

            // OLD NAME-HANDLING CODE
            // llvm::raw_string_ostream ss(name);
            // ss << *v;
            // name = name.substr(name.find("%"));
            // name = name.substr(0, name.find(" "));
        }
        name = EscapeString(name);  
    
        if (isBplKeyword(name))
            name = name + "_";

        return name;
    }
    
    const Expr * SmackRep::lit(llvm::Value *v) {
        if (const llvm::ConstantInt* ci = llvm::dyn_cast<llvm::ConstantInt>(v)) {
            if (ci->getBitWidth() == 1)
                return Expr::lit(!ci->isZero());
        
            uint64_t val = ci->getLimitedValue();
            if (width > 0 && ci->isNegative())
                return Expr::fn(SUB, Expr::lit(0,width), Expr::lit(-val,width));
            else
                return Expr::lit(val,width);
        
        } else if (llvm::isa<llvm::ConstantPointerNull>(v))
            return Expr::lit(0,width);
        
         else
             return off(expr(v));
            // assert( false && "value type not supported" );
    }
     
    const Expr * SmackRep::lit(unsigned v) {
        // TODO why doesn't this one do the thing with negative as well?
        return Expr::lit(v,width);
    }
    
    const Expr * SmackRep::ptrArith(
        llvm::Value *p, vector<llvm::Value*> ps, vector<llvm::Type*> ts) {

        assert ( ps.size() > 0 && ps.size() == ts.size() );

        const Expr *e = expr(p);
        
        for (unsigned i=0; i<ps.size(); i++) {
            if (llvm::StructType *st = llvm::dyn_cast<llvm::StructType>(ts[i])) {
            
                assert( ps[i]->getType()->isIntegerTy() 
                    && ps[i]->getType()->getPrimitiveSizeInBits() == 32 
                    && "Illegal struct idx" );

                // Get structure layout information...
                unsigned fieldNo =
                    llvm::cast<llvm::ConstantInt>(ps[i])->getZExtValue();

                // Add in the offset, as calculated by the      
                // structure layout info...
                e = pa(e, fieldOffset(st,fieldNo), 1);
                    
            } else {
                llvm::Type *et = 
                    llvm::cast<llvm::SequentialType>(ts[i])->getElementType();
                e = pa(e, lit(ps[i]), storageSize(et));
            }
        }

        return e;
    }

    const Expr * SmackRep::expr(llvm::Value *v) {
        using namespace llvm;
        
        if (GlobalValue *g = dyn_cast<GlobalValue>(v)) {
            assert(g->hasName());
            return ptr(Expr::id(id(v)),lit((unsigned)0));
        
        } else if (v->hasName())
            return Expr::id(id(v));
        
        else if (Constant* constant = dyn_cast<Constant>(v)) {

            if (ConstantExpr* constantExpr = dyn_cast<ConstantExpr>(constant)) {
            
                if (constantExpr->getOpcode() == Instruction::GetElementPtr) {

                    vector<llvm::Value*> ps;
                    vector<llvm::Type*> ts;
                    llvm::gep_type_iterator typeI = gep_type_begin(constantExpr);
                    for (unsigned i=1; i<constantExpr->getNumOperands(); i++, ++typeI) {
                        ps.push_back(constantExpr->getOperand(i));
                        ts.push_back(*typeI);
                    }
                    return ptrArith(constantExpr->getOperand(0),ps,ts);
                
                } else if (constantExpr->getOpcode() == Instruction::BitCast)

                    // TODO: currently this is a noop instruction
                    return expr(constantExpr->getOperand(0));
                  
                else if (constantExpr->getOpcode() == Instruction::IntToPtr)

                    // TODO test this out, formerly Expr::id("$UNDEF");
                    return i2p(expr(constantExpr->getOperand(0)));
                
                else if (constantExpr->getOpcode() == Instruction::PtrToInt)

                    // TODO test this out, formerly Expr::id("$UNDEF");
                    return p2i(expr(constantExpr->getOperand(0)));

                else {
                    DEBUG(errs() << "VALUE : " << *v << "\n");
                    assert( false && "constant expression of this type not supported" );
                }

            } else if (ConstantInt* ci = dyn_cast<ConstantInt>(constant)) {
                if (ci->getBitWidth() == 1)
                    return Expr::lit(!ci->isZero());

                else return ptr(NUL, lit(ci));

            } else if (constant->isNullValue())
                return ZERO;
            
            else if (isa<UndefValue>(constant))
                return UNDEF;

            else {
                DEBUG(errs() << "VALUE : " << *v << "\n");
                assert( false && "this type of constant not supported" );
            }
            
        } else {
            DEBUG(errs() << "VALUE : " << *v << "\n");
            assert( false && "value of this type not supported" );
        }    
    }
    
    const Expr * SmackRep::op(llvm::BinaryOperator& o) {
        string op;
        switch (o.getOpcode()) {
            using llvm::Instruction;
            case Instruction::Add: op = ADD; break;
            case Instruction::Sub: op = SUB; break;
            case Instruction::Mul: op = MUL; break;
            case Instruction::SDiv: op = SDIV; break;
            case Instruction::UDiv: op = UDIV; break;
            case Instruction::SRem: op = SREM; break;
            case Instruction::URem: op = UREM; break;
            case Instruction::And: op = AND; break;
            case Instruction::Or: op = OR; break;
            case Instruction::Xor: op = XOR; break;
            case Instruction::LShr: op = LSHR; break;
            case Instruction::AShr: op = ASHR; break;
            case Instruction::Shl: op = SHL; break;
            default: 
            assert( false && "unexpected predicate." );
        }
        llvm::Value 
            *l = o.getOperand(0),
            *r = o.getOperand(1);

        const Expr *e = Expr::fn(op, 
            (isBool(l) ? b2i(expr(l)) : off(expr(l))),
            (isBool(r) ? b2i(expr(r)) : off(expr(r))) );

        return isBool(&o) ? i2b(e) : ptr(NUL, e);
    }
    
    const Expr * SmackRep::pred(llvm::CmpInst& ci) {
        const Expr *e = NULL;
        string o;
        const Expr 
            *l = expr(ci.getOperand(0)),
            *r = expr(ci.getOperand(1));
        
        switch (ci.getPredicate()) {
            using llvm::ICmpInst;
            case ICmpInst::ICMP_EQ: e = Expr::eq(l,r); break;
            case ICmpInst::ICMP_NE: e = Expr::neq(l,r); break;
            case ICmpInst::ICMP_SGE: o = SGE; break;
            case ICmpInst::ICMP_UGE: o = UGE; break;
            case ICmpInst::ICMP_SLE: o = SLE; break;
            case ICmpInst::ICMP_ULE: o = ULE; break;
            case ICmpInst::ICMP_SLT: o = SLT; break;
            case ICmpInst::ICMP_ULT: o = ULT; break;
            case ICmpInst::ICMP_SGT: o = SGT; break;
            case ICmpInst::ICMP_UGT: o = UGT; break;
            default:
            assert( false && "unexpected predicate." );
        }
        
        return e == NULL ? Expr::fn(o, off(l), off(r)) : e;
    }

} // namespace smack
