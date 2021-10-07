//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef REWRITEBITWISEOPS_H
#define REWRITEBITWISEOPS_H

#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include <boost/optional.hpp>

namespace smack {

class RewriteBitwiseOps : public llvm::ModulePass {
public:
  enum class SpecialCase {
    Shr,      // Right shift
    Shl,      // Left shift
    AndPoTMO, // And power of 2 minus 1
    AndNPoT   // And negative power of 2
  };
  static char ID; // Pass identification, replacement for typeid
  RewriteBitwiseOps() : llvm::ModulePass(ID) {}
  virtual llvm::StringRef getPassName() const;
  virtual bool runOnModule(llvm::Module &m);

private:
  boost::optional<SpecialCase> getSpecialCase(llvm::Instruction *i);
  static llvm::Instruction *rewriteShift(llvm::Instruction::BinaryOps,
                                         llvm::Instruction *);
  static llvm::Instruction *rewriteShr(llvm::Instruction *);
  static llvm::Instruction *rewriteShl(llvm::Instruction *);
  static llvm::Instruction *rewriteAndPoTMO(llvm::Instruction *);
  static llvm::Instruction *rewriteAndNPoT(llvm::Instruction *);
  llvm::Instruction *rewriteSpecialCase(SpecialCase, llvm::Instruction *);
  boost::optional<llvm::Instruction *> rewriteGeneralCase(llvm::Instruction *);
};
} // namespace smack

#endif // REWRITEBITWISEOPS_H
