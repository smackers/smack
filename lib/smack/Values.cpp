#include "Values.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/Regex.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Support/InstVisitor.h"
#include <sstream>

namespace smack {
    
    using llvm::Regex;
    using llvm::SmallVector;
    using llvm::StringRef;
    using namespace std;
    
    // TODO Do the following functions belong here ?

    string EscapeString(string str) {
      str = llvm::DOT::EscapeString(str);
      return str;
    }

    Regex BPL_KW(
      "^(bool|int|false|true|old|forall|exists|requires|modifies|ensures|invariant"
      "|free|unique|finite|complete|type|const|function|axiom|var|procedure"
      "|implementation|where|returns|assume|assert|havoc|call|return|while"
      "|break|goto|if|else)$" );
    Regex SMACK_NAME(".*__SMACK_.*");

    bool isBplKeyword(string s) {
      return BPL_KW.match(s);
    }

    bool isSmackProc(string s) {
      return SMACK_NAME.match(s);
    }

    // TODO Make this width a parameter to generate bitvector-based code.
    const int width = 0;
    
    // TODO The rest of these functions are kind of a mess, without a clear
    // and understandable interface; they are also fully of messy code, and
    // probably redundancy.

    Expr * Values::asLit(llvm::Value *v) {
        if (const llvm::ConstantInt* ci = llvm::dyn_cast<llvm::ConstantInt>(v)) {
            if (ci->getBitWidth() == 1)
                return Expr::lit(!ci->isZero());
        
            uint64_t val = ci->getLimitedValue();
            if (width > 0 && ci->isNegative())
                return Expr::fn("$sub", Expr::lit(0,width), Expr::lit(-val,width));
            else
                return Expr::lit(val,width);
        
        } else if (llvm::isa<llvm::ConstantPointerNull>(v))
            return Expr::lit(0,width);
        
         else
             return Expr::fn("$off", asExpr(v));
            // assert( false && "value type not supported" );
    }
     
    Expr * Values::asLit(unsigned v) {
        // TODO why doesn't this one do the thing with negative as well?
        return Expr::lit(v,width);
    }
    
    string Values::asId(const llvm::Value *v) {
        string name;
    
        if (v->hasName()) {
            name = v->getName().str();

            if (llvm::isa<llvm::Function>(v)) {
                stringstream ss;
                ss << name << "#ptr";
                name = ss.str();
            }        
        } else {
            // DEBUG(errs() << "Value : " << *val << "\n");
            llvm::raw_string_ostream ss(name);
            ss << *v;
            // name = name.substr(1);
            // name = "$" + EscapeString(name.substr(name.find("%")+1));
        }
        name = EscapeString(name);  
    
        if (isBplKeyword(name))
            name = name + "_";

        return name;
    }

    string Values::asFnId(llvm::Value *v) {
        if (v->hasName())
            return v->getName().str();
        else
            assert( false && "expected named value." );
    }
    
    Expr * Values::gepAsExpr(llvm::Value *p, vector<llvm::Value*> ps, vector<llvm::Type*> ts) {
        assert ( ps.size() > 0 && ps.size() == ts.size() );

        Expr *e = asExpr(p);
        
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
                e = Expr::fn("$pa", e, 
                    Expr::lit((int) fieldOffset(st,fieldNo)),
                    Expr::lit(1));
                    
            } else {
                llvm::Type *et = 
                    llvm::cast<llvm::SequentialType>(ts[i])->getElementType();
                e = Expr::fn("$pa", e, asLit(ps[i]), 
                    Expr::lit((int) storageSize(et)));
            }
        }

        return e;
    }

    Expr * Values::asExpr(llvm::Value *v) {
        using namespace llvm;
        
        if (v->hasName())
            return Expr::id(asId(v));

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
                    return gepAsExpr(constantExpr->getOperand(0),ps,ts);
                
                } else if (constantExpr->getOpcode() == Instruction::BitCast)
                    // TODO: currently this is a noop instruction
                    return asExpr( constantExpr->getOperand(0) );
                  
                else if (constantExpr->getOpcode() == Instruction::IntToPtr)
                    // TODO test this out, formerly Expr::id("$UNDEF");
                    return Expr::fn("$i2p", asExpr(constantExpr->getOperand(0)));
                
                else if (constantExpr->getOpcode() == Instruction::PtrToInt)
                    // TODO test this out, formerly Expr::id("$UNDEF");
                    return Expr::fn("$p2i", asExpr(constantExpr->getOperand(0)));

                else {
                    DEBUG(errs() << "VALUE : " << *v << "\n");
                    assert( false && "constant expression of this type not supported" );
                }

            } else if (ConstantInt* ci = dyn_cast<ConstantInt>(constant)) {
                if (ci->getBitWidth() == 1)
                    return Expr::lit(!ci->isZero());

                else return Expr::fn("$ptr", Expr::id("$NULL"), asLit(ci));

            } else if (constant->isNullValue())
                return Expr::fn("$ptr", Expr::id("$NULL"), asLit((unsigned)0));
            
            else if (isa<UndefValue>(constant))
                return Expr::id("$UNDEF");

            else {
                DEBUG(errs() << "VALUE : " << *v << "\n");
                assert( false && "this type of constant not supported" );
            }
            
        } else {
            DEBUG(errs() << "VALUE : " << *v << "\n");
            assert( false && "value of this type not supported" );
        }    
    }

    Expr * Values::asIntExpr(llvm::Value *o) {
        if (o->getType()->isIntegerTy(1))
            return Expr::fn("$b2i", asExpr(o));
        else
            return Expr::fn("$off", asExpr(o));
    }
    
    unsigned Values::storageSize(llvm::Type *t) {
        return targetData->getTypeStoreSize(t);
    }
    
    unsigned Values::fieldOffset(llvm::StructType *t, unsigned fieldNo) {
        return targetData->getStructLayout(t)->getElementOffset(fieldNo);
    }

} // namespace smack
