//
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef PRELUDE_H
#define PRELUDE_H

#include "smack/SmackRep.h"
#include "smack/BoogieAst.h"

#include <string>

namespace smack {
typedef std::list<FuncDecl*> FuncsT;

struct Op {
  enum OpType { B, I, U };
  private:
    const OpType type;
  public:
    OpType getOpType() const { return type; }
    Op(OpType type) : type(type) {}
};

struct IntOp {
  typedef const Attr* (*attrT)(std::string);
  typedef const Expr* (*exprT)(unsigned);

  std::string opName;
  unsigned arity;
  Op* intOp;
  Op* bvOp;
  bool alsoUsedByPtr;

  IntOp(std::string opName, unsigned arity, Op* intOp, Op* bvOp, bool alsoUsedByPtr) :
    opName(opName), arity(arity), intOp(intOp), bvOp(bvOp), alsoUsedByPtr(alsoUsedByPtr) {}
  //virtual FuncsT getIntFuncs(unsigned) const = 0;
  //virtual FuncsT getBvFuncs(unsigned) const = 0;
  virtual FuncsT getFuncs(unsigned) const = 0;
  static const Attr* bvAttrFunc(std::string opName);
  static const Attr* intAttrFunc(std::string opName);
};

struct FpOp {
  typedef const Attr* (*attrT)(std::string);

  std::string opName;
  unsigned arity;
  Op* op;

  FpOp(std::string opName, unsigned arity, Op* op) :
    opName(opName), arity(arity), op(op) {}
  virtual Decl* getModeledFpFunc(unsigned) const = 0;
  virtual Decl* getUninterpretedFpFunc() const = 0;
  static const Attr* fpAttrFunc(std::string opName);
};

template<typename ATTRT>
struct BuiltinOp : public Op {
  typedef const Attr* (*attrT)();
  attrT func;
  BuiltinOp(ATTRT func) : Op(B), func((attrT)func) {}
  static bool classof(const Op* op) {
    return op->getOpType() == B;
  }
};

template<typename EXPRT>
struct InlinedOp : public Op {
  typedef const Expr* (*exprT)();
  exprT func;
  InlinedOp(EXPRT func) : Op(I), func((exprT)func) {}
  static bool classof(const Op* op) {
    return op->getOpType() == I;
  }
};

struct UninterpretedOp : public Op {
  UninterpretedOp() : Op(U) {}
  static bool classof(const Op* op) {
    return op->getOpType() == U;
  }
};

class Prelude;
struct Gen {
  Prelude& prelude;

  Gen(Prelude& prelude) : prelude(prelude) {}
  virtual void generate(std::stringstream& s) const = 0;
};

struct TypeGen : public Gen {
  TypeGen(Prelude& prelude) : Gen(prelude) {}
  virtual void generateArithOps(std::stringstream& s) const = 0;
  virtual void generatePreds(std::stringstream& s) const = 0;
  virtual void generateMemOps(std::stringstream& s) const = 0;
  virtual void generateConvOps(std::stringstream& s) const = 0;
  virtual void generateExtractValueFuncs(std::stringstream& s) const = 0;
};

struct IntOpGen: public TypeGen {
  struct IntArithOp;
  struct IntPred;
  struct IntConv;

  IntOpGen(Prelude& prelude) : TypeGen(prelude) {}

  static const std::vector<unsigned> INTEGER_SIZES;

  void generateArithOps(std::stringstream& s) const;
  void generatePreds(std::stringstream& s) const;
  void generateMemOps(std::stringstream& s) const;
  void generateConvOps(std::stringstream& s) const;
  void generateExtractValueFuncs(std::stringstream& s) const;
  void generateBvIntConvs(std::stringstream& s) const;
  void generate(std::stringstream& s) const;
};

struct PtrOpGen: public TypeGen {
  PtrOpGen(Prelude& prelude) : TypeGen(prelude) {}

  void generateArithOps(std::stringstream& s) const;
  void generatePreds(std::stringstream& s) const;
  void generateMemOps(std::stringstream& s) const;
  void generateConvOps(std::stringstream& s) const;
  void generateExtractValueFuncs(std::stringstream& s) const;
  void generatePtrNumConvs(std::stringstream& s) const;
  void generate(std::stringstream& s) const;
};

struct FpOpGen: public TypeGen {
  struct FpArithOp;
  struct FpPred;
  struct FpIntConv;

  FpOpGen(Prelude& prelude) : TypeGen(prelude) {}

  static const std::map<unsigned, std::pair<unsigned, unsigned>> FP_LAYOUT;
  static const std::vector<unsigned> FP_BIT_WIDTHS;

  void generateArithOps(std::stringstream& s) const;
  void generatePreds(std::stringstream& s) const;
  void generateMemOps(std::stringstream& s) const;
  void generateConvOps(std::stringstream& s) const;
  void generateExtractValueFuncs(std::stringstream& s) const;
  void generateFpIntConv(std::stringstream& s) const;
  void generate(std::stringstream& s) const;
};

struct TypeDeclGen: public Gen {
  TypeDeclGen(Prelude& prelude) : Gen(prelude) {}
  void generate(std::stringstream& s) const;
};

struct ConstDeclGen: public Gen {
  ConstDeclGen(Prelude& prelude) : Gen(prelude) {}
  void generatePtrConstant(unsigned val, std::stringstream& s) const;
  void generateIntConstant(unsigned val, std::stringstream& s) const;
  void generate(std::stringstream& s) const;
};

struct MemDeclGen: public Gen {
  MemDeclGen(Prelude& prelude) : Gen(prelude) {}
  void generateMemoryMaps(std::stringstream& s) const;
  void generateAddrBoundsAndPred(std::stringstream& s) const;
  void generateGlobalAllocations(std::stringstream& s) const;
  void generate(std::stringstream& s) const;
};

class Prelude {
  TypeDeclGen* typeDeclGen;
  ConstDeclGen* constDeclGen;
  MemDeclGen* memDeclGen;
  IntOpGen* intOpGen;
  PtrOpGen* ptrOpGen;
  FpOpGen* fpOpGen;

public:
  SmackRep &rep;

  Prelude(SmackRep &rep) : rep(rep) {
    typeDeclGen = new TypeDeclGen(*this);
    constDeclGen = new ConstDeclGen(*this);
    memDeclGen = new MemDeclGen(*this);
    intOpGen = new IntOpGen(*this);
    ptrOpGen = new PtrOpGen(*this);
    fpOpGen = new FpOpGen(*this);
  }

  std::string getPrelude();
  const Expr* mapSelExpr (unsigned idx);
  const Expr* mapUpdExpr (unsigned idx, const Expr* val, const Expr* map = nullptr);
  FuncDecl* safeLoad(std::string elemType);
  FuncDecl* unsafeLoad(std::string elemType, const Expr* body, bool bytes = true);
  FuncDecl* safeStore(Binding elemBinding);
  FuncDecl* unsafeStore(Binding elemBinding, const Expr* body, bool bytes = true);
};

}

#endif // PRELUDE_H
