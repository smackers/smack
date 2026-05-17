//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/BplFilePrinter.h"
#include "smack/BoogieAst.h"
#include "smack/InitializePasses.h"
#include "smack/SmackModuleGenerator.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GraphWriter.h"
#include <sstream>

namespace smack {

using llvm::errs;

} // namespace smack

char smack::BplFilePrinter::ID = 0;

using namespace llvm;
using namespace smack;
INITIALIZE_PASS(BplFilePrinter, "bpl-file-printer", "Boogie file printing",
                false, false)

namespace smack {

void BplFilePrinter::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<SmackModuleGenerator>();
}

bool BplFilePrinter::runOnModule(llvm::Module &m) {
  SmackModuleGenerator &smackGenerator = getAnalysis<SmackModuleGenerator>();
  Program *program = smackGenerator.getProgram();
  std::ostringstream s;
  program->print(s);
  out << s.str();
  // DEBUG_WITH_TYPE("bpl", errs() << "" << s.str());
  return false;
}

llvm::PreservedAnalyses
BplFilePrinterNewPM::run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  auto &smgResult = MAM.getResult<SmackModuleGeneratorAnalysis>(M);
  Program *program = smgResult.getProgram();
  std::ostringstream s;
  program->print(s);
  out << s.str();
  return llvm::PreservedAnalyses::all();
}
} // namespace smack
