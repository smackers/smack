//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef MODS_H
#define MODS_H

#include "smack/SmackModuleGenerator.h"

namespace smack {

class GenModifies : public llvm::ModulePass {

private:
  std::stack<std::string> st;
  std::map<std::string, bool> onStack;
  std::map<std::string, int> index;
  std::map<std::string, int> low;
  std::map<std::string, int> SCCOfProc;
  std::map<std::string, ProcDecl*> proc;
  std::vector<std::set<int>> SCCGraph;
  std::vector<std::set<std::string>> modVars;

  int maxIndex;

  void genSCC(ProcDecl *proc);
  void genSCCGraph(ProcDecl *proc);
  void calcModifies(ProcDecl *proc);

public:
  static char ID; // Pass identification, replacement for typeid

  GenModifies() : llvm::ModulePass(ID), maxIndex(1) {}

  virtual bool runOnModule(llvm::Module& m);

  virtual const char *getPassName() const {
    return "Modifies clause generation";
  }

  virtual void getAnalysisUsage(llvm::AnalysisUsage& AU) const {
    AU.setPreservesAll();
    AU.addRequired<SmackModuleGenerator>();
  } 
};
}

#endif // MODS_H

