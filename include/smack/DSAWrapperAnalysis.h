//
// This file is distributed under the MIT License. See LICENSE for details.
//
// NewPM bridge: expose the legacy `smack::DSAWrapper` ModulePass (now backed by
// SVF's Andersen points-to + union-find region partition) as a NewPM
// ModuleAnalysis. The analysis owns a `legacy::PassManager` for the lifetime of
// the cached result; the wrapped `DSAWrapper*` is non-owning (the legacy PM owns
// it). Consumer NewPM passes obtain `Result` via
// `MAM.getResult<DSAWrapperAnalysis>(M)` and call its forwarding methods.
//
// NOTE: the canonical, proven path is the LEGACY PassManager (SMACK defaults to
// SMACK_NEW_PM=OFF). This NewPM bridge only needs to compile.
//

#ifndef SMACK_DSAWRAPPER_ANALYSIS_H
#define SMACK_DSAWRAPPER_ANALYSIS_H

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/PassManager.h"

#include "smack/DSAWrapper.h"

#include <memory>

namespace smack {

class DSAWrapperAnalysis
    : public llvm::AnalysisInfoMixin<DSAWrapperAnalysis> {
  friend llvm::AnalysisInfoMixin<DSAWrapperAnalysis>;
  static llvm::AnalysisKey Key;

public:
  // Result holds a legacy PassManager keeping DSAWrapper alive for as long as
  // MAM caches this analysis. The `wrapper` pointer is non-owning; PM owns it.
  struct Result {
    std::unique_ptr<llvm::legacy::PassManager> pm;
    DSAWrapper *wrapper = nullptr;

    // Forward every DSAWrapper public method so NewPM consumers can call
    // these on the Result without dereferencing `wrapper` themselves.
    bool isStaticInitd(MemNodeRef n) { return wrapper->isStaticInitd(n); }
    bool isMemOpd(MemNodeRef n) { return wrapper->isMemOpd(n); }
    bool isRead(const llvm::Value *V) { return wrapper->isRead(V); }
    unsigned getPointedTypeSize(const llvm::Value *v) {
      return wrapper->getPointedTypeSize(v);
    }
    unsigned getOffset(const llvm::Value *v) { return wrapper->getOffset(v); }
    MemNodeRef getNode(const llvm::Value *v) { return wrapper->getNode(v); }
    bool isTypeSafe(const llvm::Value *v) { return wrapper->isTypeSafe(v); }
    unsigned getNumGlobals(MemNodeRef n) { return wrapper->getNumGlobals(n); }

    // MAM invalidation hook. Honor explicit preservation: invalidate when a
    // transform reports `none()`. Consumers (Regions, SmackModuleGenerator)
    // re-request the analysis on each pass entry so they always see the live
    // `wrapper`.
    bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &PA,
                    llvm::ModuleAnalysisManager::Invalidator &) {
      auto PAC = PA.getChecker<DSAWrapperAnalysis>();
      return !PAC.preserved() &&
             !PAC.preservedSet<llvm::AllAnalysesOn<llvm::Module>>();
    }
  };

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
};

} // namespace smack

#endif // SMACK_DSAWRAPPER_ANALYSIS_H
