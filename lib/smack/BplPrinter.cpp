//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "BplPrinter.h"
#include <sstream>

using namespace smack;

RegisterPass<BplPrinter> Y("bpl_print", "BoogiePL printer pass");
char BplPrinter::ID = 0;

bool BplPrinter::runOnModule(Module &m) {
  SmackGenerator& smackGenerator = getAnalysis<SmackGenerator>();
  Program *program = smackGenerator.getProgram();
  ostringstream s;
  program->print(s);  
  DEBUG_WITH_TYPE("bpl", errs() << "" << s.str());
  return false;
}
