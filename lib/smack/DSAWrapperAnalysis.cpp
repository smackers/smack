//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/DSAWrapperAnalysis.h"

#include "llvm/InitializePasses.h"

#include "smack/InitializePasses.h"

namespace smack {

llvm::AnalysisKey DSAWrapperAnalysis::Key;

DSAWrapperAnalysis::Result
DSAWrapperAnalysis::run(llvm::Module &M,
                        llvm::ModuleAnalysisManager & /*MAM*/) {
  Result r;

  // The SVF-backed DSAWrapper runs SVF directly inside runOnModule and has no
  // LLVM/sea-dsa analysis dependency, so a bare legacy PM with just the wrapper
  // suffices.
  r.pm = std::make_unique<llvm::legacy::PassManager>();
  auto *dsa = new DSAWrapper();
  r.wrapper = dsa;
  r.pm->add(dsa); // PM takes ownership
  r.pm->run(M);
  return r;
}

} // namespace smack
