//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/BplPrinter.h"
#include "smack/BoogieAst.h"
#include "smack/SmackModuleGenerator.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GraphWriter.h"
#include <sstream>

namespace smack {

using llvm::errs;

llvm::RegisterPass<BplPrinter> Y("bpl_print", "BoogiePL printer pass");
char BplPrinter::ID = 0;

void BplPrinter::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<SmackModuleGenerator>();
}

bool BplPrinter::runOnModule(llvm::Module &m) {
  SmackModuleGenerator &smackGenerator = getAnalysis<SmackModuleGenerator>();
  Program *program = smackGenerator.getProgram();
  std::ostringstream s;
  program->print(s);
  DEBUG_WITH_TYPE("bpl", errs() << "" << s.str());
  return false;
}
} // namespace smack
