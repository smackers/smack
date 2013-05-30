#include "Values.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/Regex.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Support/InstVisitor.h"
#include <sstream>

using namespace llvm;

namespace smack {

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
    Regex CPP_NAMETX("(_ZN?[0-9]*)([A-Za-z0-9_$#@!?]+)(i|pv)");

    string strip(string s) {
      SmallVector<StringRef,4> matches;
      if (CPP_NAMETX.match(s,&matches))
        return matches[2];
      else
        return s;
    }

    bool isBplKeyword(string s) {
      return BPL_KW.match(s);
    }

    bool isSmackProc(string s) {
      return SMACK_NAME.match(s);
    }

    const int width = 0;

    Expr * Values::lit(Value *v) {
        if (const ConstantInt* ci = dyn_cast<ConstantInt>(v)) {
            if (ci->getBitWidth() == 1)
                return Expr::lit(!ci->isZero());
        
            uint64_t val = ci->getLimitedValue();
            if (width > 0 && ci->isNegative())
                return Expr::fn("$sub", Expr::lit(0,width), Expr::lit(-val,width));
            else
                return Expr::lit(val,width);
        
        } else if (isa<ConstantPointerNull>(v))
            return Expr::lit(0,width);
        
         else
             return Expr::fn("$off",expr(v));
            // assert( false && "value type not supported" );
    }
     
    Expr * Values::lit(unsigned v) {
        // TODO why doesn't this one do the thing with negative as well?
        return Expr::lit(v,width);
    }
    
    string Values::id(const Value *v) {
        string name;
    
        if (v->hasName()) {
            name = strip( v->getName().str() );

            if (isa<Function>(v)) {
                stringstream ss;
                ss << name << "#ptr";
                name = ss.str();
            }        
        } else {
            // DEBUG(errs() << "Value : " << *val << "\n");
            raw_string_ostream ss(name);
            ss << *v;
            // name = name.substr(1);
            // name = "$" + EscapeString(name.substr(name.find("%")+1));
        }
        name = EscapeString(name);  
    
        if (isBplKeyword(name))
            name = name + "_";

        return name;
    }

    string Values::fun(Value *v) {
        if (v->hasName())
            return strip(v->getName().str());
        else
            assert( false && "expected named value." );
    }

    Expr * Values::expr(Value *v) {
        if (v->hasName())
            return Expr::id(id(v));        

        else if (Constant* constant = dyn_cast<Constant>(v)) {

            if (ConstantExpr* constantExpr = dyn_cast<ConstantExpr>(constant)) {
            
                if (constantExpr->getOpcode() == Instruction::GetElementPtr) {

                    unsigned n = constantExpr->getNumOperands();
                    Value* pv = constantExpr->getOperand(0);
                    Expr *p = expr(pv);

                    Type* type = pv->getType();
                    gep_type_iterator typeI = gep_type_begin(constantExpr);
                
                    for (unsigned i = 1; i < n; i++, ++typeI) {
                    
                        Constant* idx = constantExpr->getOperand(i);
                    
                        if (StructType* structType = dyn_cast<StructType>(*typeI)) {
                        
                            assert( idx->getType()->isIntegerTy() 
                                && idx->getType()->getPrimitiveSizeInBits() == 32 
                                && "Illegal struct idx" );

                            // Get structure layout information...
                            const StructLayout* layout = targetData->getStructLayout(structType);
                            unsigned fieldNo = cast<ConstantInt>(idx)->getZExtValue();

                            // Add in the offset, as calculated by the      
                            // structure layout info...
                            p = Expr::fn("$pa", p, 
                                Expr::lit((int) layout->getElementOffset(fieldNo)),
                                Expr::lit(1));

                            // Update type to refer to current element
                            type = structType->getElementType(fieldNo);
                        
                        } else {
                            // Update type to refer to current element
                            type = cast<SequentialType>(type)->getElementType();
                            p = Expr::fn("$pa", p, lit(idx), 
                                Expr::lit((int) targetData->getTypeStoreSize(type)));
                        }
                    }
                    return p;
                
                } else if (constantExpr->getOpcode() == Instruction::BitCast)

                      // TODO: currently this is a noop instruction
                      return expr( constantExpr->getOperand(0) );
                  
                else if (constantExpr->getOpcode() == Instruction::IntToPtr)
                    return Expr::id("$UNDEF");

                else
                    assert( false && "constant expression of this type not supported" );

            } else if (ConstantInt* ci = dyn_cast<ConstantInt>(constant)) {
                if (ci->getBitWidth() == 1)
                    return Expr::lit(!ci->isZero());

                else return Expr::fn("$ptr", Expr::id("$NULL"), lit(ci));

            } else if (constant->isNullValue())
                return Expr::fn("$ptr", Expr::id("$NULL"), lit((unsigned)0));
            
            else if (isa<UndefValue>(constant))
                return Expr::id("$UNDEF");

            else
                assert( false && "this type of constant not supported" );
            
        } else {
            assert( false && "value of this type not supported" );
        }    
    }

    Expr * Values::integer(Value *o) {
        if (o->getType()->isIntegerTy(1))
            return Expr::fn("$b2i", expr(o));
        else
            return Expr::fn("$off", expr(o));
    }
    
    unsigned Values::storageSize(Type *t) {
        return targetData->getTypeStoreSize(t);
    }
    
    unsigned Values::fieldOffset(StructType *t, unsigned fieldNo) {
        return targetData->getStructLayout(t)->getElementOffset(fieldNo);
    }
}
