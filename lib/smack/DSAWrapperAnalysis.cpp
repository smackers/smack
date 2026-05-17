//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/DSAWrapperAnalysis.h"

#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/InitializePasses.h"

#include "seadsa/AllocWrapInfo.hh"
#include "seadsa/CompleteCallGraph.hh"
#include "seadsa/DsaAnalysis.hh"
#include "seadsa/DsaLibFuncInfo.hh"
#include "seadsa/InitializePasses.hh"
#include "seadsa/support/RemovePtrToInt.hh"

#include "smack/InitializePasses.h"

namespace smack {

llvm::AnalysisKey DSAWrapperAnalysis::Key;

DSAWrapperAnalysis::Result
DSAWrapperAnalysis::run(llvm::Module &M,
                        llvm::ModuleAnalysisManager & /*MAM*/) {
  Result r;

  // Ensure every legacy pass we touch is registered. Idempotent across
  // multiple invocations.
  auto &Reg = *llvm::PassRegistry::getPassRegistry();
  llvm::initializeCore(Reg);
  llvm::initializeAnalysis(Reg);
  llvm::initializeTransformUtils(Reg);
  llvm::initializeRemovePtrToIntPass(Reg);
  llvm::initializeAllocWrapInfoPass(Reg);
  llvm::initializeDsaLibFuncInfoPass(Reg);
  llvm::initializeDsaAnalysisPass(Reg);

  r.pm = std::make_unique<llvm::legacy::PassManager>();

  // Stand up sea-dsa's required analyses. LegacyPM auto-resolves additional
  // transitively-required passes (LoopInfo, TargetLibraryInfo, etc.) via
  // registry lookups, but we add the ones whose construction has a side
  // effect SMACK already relies on (RemovePtrToInt mirrors the legacy
  // SmackPipeline.cpp line that adds `seadsa::createRemovePtrToIntPass()`).
  r.pm->add(seadsa::createRemovePtrToIntPass());

  // DSAWrapper requests `seadsa::DsaAnalysis` via addRequiredTransitive,
  // and DsaAnalysis transitively requires AllocWrapInfo, DsaLibFuncInfo,
  // CallGraphWrapperPass, TargetLibraryInfoWrapperPass, LoopInfoWrapperPass.
  // LegacyPassManager instantiates them on-demand because the initializers
  // above registered them.
  auto *dsa = new DSAWrapper();
  r.wrapper = dsa;
  r.pm->add(dsa); // PM takes ownership

  r.pm->run(M);
  return r;
}

llvm::AnalysisKey CompleteCallGraphAnalysis::Key;

CompleteCallGraphAnalysis::Result
CompleteCallGraphAnalysis::run(llvm::Module &M,
                               llvm::ModuleAnalysisManager & /*MAM*/) {
  Result r;

  auto &Reg = *llvm::PassRegistry::getPassRegistry();
  llvm::initializeCore(Reg);
  llvm::initializeAnalysis(Reg);
  llvm::initializeTransformUtils(Reg);
  llvm::initializeRemovePtrToIntPass(Reg);
  llvm::initializeAllocWrapInfoPass(Reg);
  llvm::initializeDsaLibFuncInfoPass(Reg);
  llvm::initializeDsaAnalysisPass(Reg);
  llvm::initializeCompleteCallGraphPass(Reg);

  r.pm = std::make_unique<llvm::legacy::PassManager>();
  r.pm->add(seadsa::createRemovePtrToIntPass());
  auto *ccg = new seadsa::CompleteCallGraph();
  r.ccg = ccg;
  r.pm->add(ccg);
  r.pm->run(M);
  return r;
}

} // namespace smack
