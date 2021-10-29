//
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef PRELUDE_H
#define PRELUDE_H

#include "smack/BoogieAst.h"
#include "smack/SmackRep.h"

#include <string>

namespace smack {
typedef std::list<FuncDecl *> FuncsT;

// function declaration type
struct Op {
  enum OpType { Builtin, Inlined, Uninterpreted };

private:
  const OpType type;

public:
  OpType getOpType() const { return type; }
  Op(OpType type) : type(type) {}
};

// represent a set of integer operations such as $add.<T>,
// where `T` is an integer type parameterized by integer bit-width
// the virtual method `getFuncs` therefore generates a set of
// function declarations for <$opName>.<T>.
struct IntOp {
  typedef const Attr *(*attrT)(std::string);
  typedef const Expr *(*exprT)(unsigned);

  std::string opName;
  unsigned arity;
  Op *intOp;
  Op *bvOp;
  bool alsoUsedByPtr;

  IntOp(std::string opName, unsigned arity, Op *intOp, Op *bvOp,
        bool alsoUsedByPtr)
      : opName(opName), arity(arity), intOp(intOp), bvOp(bvOp),
        alsoUsedByPtr(alsoUsedByPtr) {}
  // virtual FuncsT getIntFuncs(unsigned) const = 0;
  // virtual FuncsT getBvFuncs(unsigned) const = 0;
  virtual FuncsT getFuncs(unsigned) const = 0;
  static const Attr *bvAttrFunc(std::string opName);
  static const Attr *intAttrFunc(std::string opName);
  virtual ~IntOp(){};
};

// represent a set of integer operations such as $fadd.<T>
struct FpOp {
  typedef const Attr *(*attrT)(std::string);

  std::string opName;
  unsigned arity;
  Op *op;

  FpOp(std::string opName, unsigned arity, Op *op)
      : opName(opName), arity(arity), op(op) {}
  virtual Decl *getModeledFpFunc(unsigned) const = 0;
  virtual Decl *getUninterpretedFpFunc() const = 0;
  static const Attr *fpAttrFunc(std::string opName);
  virtual ~FpOp(){};
};

// builtin functions templated by a function type. A function
// of such type, when applied, returns an attribute
template <typename ATTRT> struct BuiltinOp : public Op {
  typedef const Attr *(*attrT)(...);
  attrT func;
  BuiltinOp(ATTRT func) : Op(Builtin), func((attrT)func) {}
  static bool classof(const Op *op) { return op->getOpType() == Builtin; }
};

// inlined functions templated by a function type. A function
// of such type, when applied, returns an expression as the function body
template <typename EXPRT> struct InlinedOp : public Op {
  typedef const Expr *(*exprT)(...);
  exprT func;
  InlinedOp(EXPRT func) : Op(Inlined), func((exprT)func) {}
  static bool classof(const Op *op) { return op->getOpType() == Inlined; }
};

// uninterpreted functions
struct UninterpretedOp : public Op {
  UninterpretedOp() : Op(Uninterpreted) {}
  static bool classof(const Op *op) { return op->getOpType() == Uninterpreted; }
};

class Prelude;
// generic generator class that produces relevant declarations
struct Gen {
  Prelude &prelude;

  Gen(Prelude &prelude) : prelude(prelude) {}
  virtual void generate(std::stringstream &s) const = 0;
  virtual ~Gen(){};
};

// generator class for integer, pointer, and floating-point types
struct TypeGen : public Gen {
  TypeGen(Prelude &prelude) : Gen(prelude) {}
  virtual void generateArithOps(std::stringstream &s) const = 0;
  virtual void generatePreds(std::stringstream &s) const = 0;
  virtual void generateMemOps(std::stringstream &s) const = 0;
  virtual void generateConvOps(std::stringstream &s) const = 0;
  virtual void generateExtractValueFuncs(std::stringstream &s) const = 0;
  virtual ~TypeGen(){};
};

// generator class for integers
struct IntOpGen : public TypeGen {
  struct IntArithOp;
  struct IntPred;
  struct IntConv;

  IntOpGen(Prelude &prelude) : TypeGen(prelude) {}

  static const std::vector<unsigned> INTEGER_SIZES;

  void generateArithOps(std::stringstream &s) const override;
  void generatePreds(std::stringstream &s) const override;
  void generateMemOps(std::stringstream &s) const override;
  void generateConvOps(std::stringstream &s) const override;
  void generateExtractValueFuncs(std::stringstream &s) const override;
  void generateBvIntConvs(std::stringstream &s) const;
  void generate(std::stringstream &s) const override;
};

// generator class for pointers
struct PtrOpGen : public TypeGen {
  PtrOpGen(Prelude &prelude) : TypeGen(prelude) {}

  void generateArithOps(std::stringstream &s) const override;
  void generatePreds(std::stringstream &s) const override;
  void generateMemOps(std::stringstream &s) const override;
  void generateConvOps(std::stringstream &s) const override;
  void generateExtractValueFuncs(std::stringstream &s) const override;
  void generatePtrNumConvs(std::stringstream &s) const;
  void generate(std::stringstream &s) const override;
};

// generator class for floats
struct FpOpGen : public TypeGen {
  struct FpArithOp;
  struct FpPred;
  struct FpIntConv;

  FpOpGen(Prelude &prelude) : TypeGen(prelude) {}

  static const std::map<unsigned, std::pair<unsigned, unsigned>> FP_LAYOUT;
  static const std::vector<unsigned> FP_BIT_WIDTHS;

  void generateArithOps(std::stringstream &s) const override;
  void generatePreds(std::stringstream &s) const override;
  void generateMemOps(std::stringstream &s) const override;
  void generateConvOps(std::stringstream &s) const override;
  void generateExtractValueFuncs(std::stringstream &s) const override;
  void generateFpIntConv(std::stringstream &s) const;
  void generate(std::stringstream &s) const override;
};

struct TypeDeclGen : public Gen {
  TypeDeclGen(Prelude &prelude) : Gen(prelude) {}
  void generate(std::stringstream &s) const override;
};

struct ConstDeclGen : public Gen {
  ConstDeclGen(Prelude &prelude) : Gen(prelude) {}
  void generatePtrConstant(unsigned val, std::stringstream &s) const;
  void generateIntConstant(unsigned val, std::stringstream &s) const;
  void generate(std::stringstream &s) const override;
};

struct MemDeclGen : public Gen {
  MemDeclGen(Prelude &prelude) : Gen(prelude) {}
  void generateMemoryMaps(std::stringstream &s) const;
  void generateAddrBoundsAndPred(std::stringstream &s) const;
  void generateGlobalAllocations(std::stringstream &s) const;
  void generate(std::stringstream &s) const override;
};

class Prelude {
  TypeDeclGen *typeDeclGen;
  ConstDeclGen *constDeclGen;
  MemDeclGen *memDeclGen;
  IntOpGen *intOpGen;
  PtrOpGen *ptrOpGen;
  FpOpGen *fpOpGen;

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
  const Expr *mapSelExpr(unsigned idx);
  const Expr *mapUpdExpr(unsigned idx, const Expr *val,
                         const Expr *map = nullptr);
  FuncDecl *safeLoad(std::string elemType);
  FuncDecl *unsafeLoad(std::string elemType, const Expr *body,
                       bool bytes = true);
  FuncDecl *safeStore(Binding elemBinding);
  FuncDecl *unsafeStore(Binding elemBinding, const Expr *body,
                        bool bytes = true);
};
} // namespace smack

#endif // PRELUDE_H
