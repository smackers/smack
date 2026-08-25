//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef INTEGEROVERFLOWCHECKER_H
#define INTEGEROVERFLOWCHECKER_H

#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include <map>

namespace smack {

/// Metadata attached to ordinary arithmetic after consuming Clang's
/// sanitizer-only overflow intrinsics. Its single string operand is `"s"` or
/// `"u"`, providing sign evidence without retaining an overflow check.
extern const char OverflowSignMetadata[];

/// Lower LLVM checked-integer arithmetic to ordinary LLVM instructions.
///
/// The early, frontend-only mode recognizes Clang sanitizer instrumentation by
/// `!nosanitize`, records its signedness in OverflowSignMetadata, replaces its
/// overflow flag with false, and removes the unreachable UBSan path. It does
/// not turn that instrumentation into a verification condition, and it
/// touches nothing but the `!nosanitize` scaffolding: the instrumented
/// arithmetic and the program around it are left exactly as Clang emitted
/// them, so later analyses see the IR of an uninstrumented compilation. The
/// normal mode retains the existing behavior for genuine checked-arithmetic
/// intrinsics and explicitly requested signed-overflow checks.
class IntegerOverflowChecker : public llvm::ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  explicit IntegerOverflowChecker(bool frontendInstrumentationOnly = false)
      : llvm::ModulePass(ID),
        FrontendInstrumentationOnly(frontendInstrumentationOnly) {}
  virtual llvm::StringRef getPassName() const override;
  virtual bool runOnModule(llvm::Module &m) override;

private:
  /// Restrict this instance to annotation-only frontend instrumentation.
  bool FrontendInstrumentationOnly;
  static const std::map<std::string, llvm::Instruction::BinaryOps>
      INSTRUCTION_TABLE;
  llvm::APInt getMax(unsigned bits, bool isSigned);
  llvm::APInt getMin(unsigned bits, bool isSigned);
  llvm::Value *extendBitWidth(llvm::Value *v, int bits, bool isSigned,
                              llvm::Instruction *i);
  llvm::BinaryOperator *createFlag(llvm::Value *v, int bits, bool isSigned,
                                   llvm::Instruction *i);
  llvm::Value *createResult(llvm::Value *v, int bits, llvm::Instruction *i);
  void addCheck(llvm::Function *co, llvm::Value *flag, llvm::Instruction *i);
  void addBlockingAssume(llvm::Function *va, llvm::Value *flag,
                         llvm::Instruction *i);
};
} // namespace smack

#endif // INTEGEROVERFLOWCHECKER_H
