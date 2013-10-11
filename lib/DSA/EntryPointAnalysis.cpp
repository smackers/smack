//===-- EntryPointAnalysis.cpp - Entry point Finding Pass -----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is a general way of finding entry points in a system.  Simple programs
// will use the main version.  Libraries and OS kernels can have more
// specialized versions.  This is done as an analysis group to allow more
// convinient opt invocations.
//
//===----------------------------------------------------------------------===//

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Debug.h"

#include <fstream>
#include <set>

#include "dsa/EntryPointAnalysis.h"

using namespace llvm;

static cl::opt<std::string> epaFile("epa-file",
       cl::desc("File with entry point names")); //, cl::ReallyHidden);

static void readNames(std::set<std::string>& names) {
  std::ifstream msf(epaFile.c_str(), std::ifstream::in);
  if (!msf.good())
    errs() << "Failed to open file: " << epaFile << " (continuing anyway)\n";
  while (msf.good()) {
    std::string n;
    msf >> n;
    if (n.size()) {
      names.insert(n);
//      errs() << "Read " << n << "\n";
    }
  }
}


EntryPointAnalysis::EntryPointAnalysis() :ModulePass(ID), haveNames(false) {
}

EntryPointAnalysis::~EntryPointAnalysis() {}

void EntryPointAnalysis::findEntryPoints(const Module& M,
                                         std::vector<const Function*>& dest) const {
  for (Module::const_iterator ii = M.begin(), ee = M.end(); ii != ee; ++ii)
    if (isEntryPoint(ii))
      dest.push_back(ii);
}

void EntryPointAnalysis::print(llvm::raw_ostream& O, const Module* M) const {
  std::vector<const Function*> d;
  findEntryPoints(*M, d);
  O << "EntryPoints: ";
  bool prev = false;
  for (std::vector<const Function*>::iterator ii = d.begin(), ee = d.end();
       ii != ee; ++ii) {
    O << (prev ? ", " : "") << (*ii)->getName().str();
    prev = true;
  }
  O << "\n";
}

bool EntryPointAnalysis::runOnModule(llvm::Module& M) {
  if (epaFile.size()) {
    haveNames = true;
    readNames(names);
  }
  return false;
}

void EntryPointAnalysis::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
}

bool EntryPointAnalysis::isEntryPoint(const llvm::Function* F) const {
  if (haveNames) {
    return !F->isDeclaration()
            && F->hasExternalLinkage()
            && F->hasName()
            && names.find(F->getName().str()) != names.end();
  } else {
    return !F->isDeclaration()
            && F->hasExternalLinkage()
            && F->hasName() && F->getName() == "main";
  }
}



char EntryPointAnalysis::ID;
static RegisterPass<EntryPointAnalysis> A("epa", "Identify EntryPoints");
