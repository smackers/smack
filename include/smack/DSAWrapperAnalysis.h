//
// This file is distributed under the MIT License. See LICENSE for details.
//
// Phase A5 Tier C bridge: expose the legacy `smack::DSAWrapper` pass (which
// itself wraps sea-dsa's still-legacy `seadsa::DsaAnalysis`) as a NewPM
// ModuleAnalysis. The analysis owns a `legacy::PassManager` for the
// lifetime of the cached result; the wrapped `DSAWrapper*` is non-owning
// (the legacy PM owns it). Consumer NewPM passes obtain `Result` via
// `MAM.getResult<DSAWrapperAnalysis>(M)` and call its forwarding methods.
//
// Without modifying sea-dsa upstream, this is the cleanest way to bring
// DSA-dependent passes (Regions, CodifyStaticInits, ExtractContracts,
// Devirtualize) and the downstream sinks (SmackModuleGenerator, BplPrinter,
// BplFilePrinter) onto a NewPM pipeline.
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
  // Result holds a legacy PassManager keeping sea-dsa + DSAWrapper alive
  // for as long as MAM caches this analysis. The `wrapper` pointer is
  // non-owning; PM owns it.
  struct Result {
    std::unique_ptr<llvm::legacy::PassManager> pm;
    DSAWrapper *wrapper = nullptr;

    // Forward every DSAWrapper public method so NewPM consumers can call
    // these on the Result without dereferencing `wrapper` themselves.
    bool isStaticInitd(const seadsa::Node *n) {
      return wrapper->isStaticInitd(n);
    }
    bool isMemOpd(const seadsa::Node *n) { return wrapper->isMemOpd(n); }
    bool isRead(const llvm::Value *V) { return wrapper->isRead(V); }
    bool isSingletonGlobal(const llvm::Value *V) {
      return wrapper->isSingletonGlobal(V);
    }
    const llvm::Type *getPointedType(const llvm::Value *v) {
      return wrapper->getPointedType(v);
    }
    unsigned getPointedTypeSize(const llvm::Value *v) {
      return wrapper->getPointedTypeSize(v);
    }
    unsigned getOffset(const llvm::Value *v) { return wrapper->getOffset(v); }
    const seadsa::Node *getNode(const llvm::Value *v) {
      return wrapper->getNode(v);
    }
    bool isTypeSafe(const llvm::Value *v) { return wrapper->isTypeSafe(v); }
    unsigned getNumGlobals(const seadsa::Node *n) {
      return wrapper->getNumGlobals(n);
    }

    // MAM invalidation hook. Honor explicit preservation: invalidate when a
    // transform reports `none()`. Devirtualize mutates the call graph so DSA
    // must rebuild against the post-devirt IR (func_ptr1.c partition fix).
    // Consumers (Regions, SmackModuleGenerator) re-request the analysis on
    // each pass entry so they always see the live `wrapper`.
    bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &PA,
                    llvm::ModuleAnalysisManager::Invalidator &) {
      auto PAC = PA.getChecker<DSAWrapperAnalysis>();
      return !PAC.preserved() &&
             !PAC.preservedSet<llvm::AllAnalysesOn<llvm::Module>>();
    }
  };

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
};

// CompleteCallGraphAnalysis: parallel NewPM bridge for sea-dsa's legacy
// `seadsa::CompleteCallGraph` pass. Used by DevirtualizeNewPM.
class CompleteCallGraphAnalysis
    : public llvm::AnalysisInfoMixin<CompleteCallGraphAnalysis> {
  friend llvm::AnalysisInfoMixin<CompleteCallGraphAnalysis>;
  static llvm::AnalysisKey Key;

public:
  struct Result {
    std::unique_ptr<llvm::legacy::PassManager> pm;
    // Non-owning pointer; owned by `pm`.
    void *ccg = nullptr; // seadsa::CompleteCallGraph* — opaque to avoid
                         // pulling sea-dsa headers into smack public API
    bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                    llvm::ModuleAnalysisManager::Invalidator &) {
      return false; // sticky cache — same lifetime rationale as DSAWrapper
    }
  };

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &);
};

} // namespace smack

#endif // SMACK_DSAWRAPPER_ANALYSIS_H
