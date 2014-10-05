//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/BplFilePrinter.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GraphWriter.h"
#include <sstream>

namespace smack {

using llvm::errs;
using namespace std;

char BplFilePrinter::ID = 0;

bool BplFilePrinter::runOnModule(llvm::Module& m) {
  SmackModuleGenerator& smackGenerator = getAnalysis<SmackModuleGenerator>();
  Program& program = smackGenerator.getProgram();
  ostringstream s;
  program.print(s);
  out << s.str();
  DEBUG_WITH_TYPE("bpl", errs() << "" << s.str());
  return false;
}
}

