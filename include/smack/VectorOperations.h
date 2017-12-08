//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef VECTOROPERATIONS_H
#define VECTOROPERATIONS_H

#include "llvm/IR/Type.h"
#include <list>

class SmackRep;
class Decl;
class FuncDecl;

using namespace llvm;

namespace smack {
  class VectorOperations {
    SmackRep *rep;
    std::string constructor(Type *T);
    std::string field(Type *T, unsigned idx);
    std::string selector(Type *T, unsigned idx);

  public:
    VectorOperations(SmackRep *rep) : rep(rep) {}
    std::list<Decl*> type(Type *T);
    FuncDecl *simd(Type *T, unsigned opcode);
    FuncDecl *shuffle(Type *T, Type *U, std::vector<int> mask);
    FuncDecl *insert(Type *T, Type *IT);
    FuncDecl *extract(Type *T, Type *IT);
    FuncDecl *load(const Value *V);
    FuncDecl *store(const Value *V);
  };
}

#endif // VECTOROPERATIONS_H
