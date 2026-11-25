//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef LOWERVARARGS_H
#define LOWERVARARGS_H

#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace smack {

// Clang lowers `va_arg` inline, walking the target's `va_list` layout, but
// `llvm.va_start` is left as a bodyless intrinsic, so the list is never
// initialized and every `va_arg` reads unconstrained memory. That is why a
// program whose result depends on a variadic argument cannot be verified.
//
// This pass supplies the missing half. For each direct call to a defined
// variadic function it clones the callee with the variadic arguments turned
// into ordinary parameters, and in the clone replaces `llvm.va_start` with
// code that lays those arguments out where the lowering will look for them:
// a buffer of one slot per argument, with the list's `overflow_arg_area`
// pointing at it and its register-save offsets exhausted, so the lowering
// always takes the overflow path. Clang's own `va_arg` code then reads the
// real values, and nothing has to recognize its shape.
//
// Because the values live in memory rather than in the clone's parameters,
// this also covers a `va_list` handed to another function, as `vfprintf`
// does. For the same reason `llvm.va_copy` becomes a copy of the list's
// fields, and `llvm.va_end`, which does nothing on this target, is removed.
//
// The layout is the System V x86-64 one, so the pass does nothing for any
// other target. A call it cannot lay out faithfully is left as it was, with
// its arguments unconstrained: one that passes a struct by value, a `long
// double`, or floating-point values together with integers or pointers.
class LowerVarArgs : public llvm::ModulePass {
public:
  static char ID;
  LowerVarArgs() : llvm::ModulePass(ID) {}
  virtual llvm::StringRef getPassName() const override;
  virtual bool runOnModule(llvm::Module &M) override;
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
};
} // namespace smack

#endif // LOWERVARARGS_H
