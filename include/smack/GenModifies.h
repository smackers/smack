//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef MODS_H
#define MODS_H

#include "smack/SmackModuleGenerator.h"
#include "smack/BoogieAst.h"
#include "llvm/Support/Regex.h"
#include <map>
#include <set>
#include <stack>

namespace smack {

using llvm::Regex;

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

  void initProcMap(Program *program);
  std::string getBplGlobalsModifiesClause(const std::set<std::string> &bplGlobals);
  void fixPrelude(Program *program, const std::string &modClause);
  void addModifiesToSmackProcs(Program *program, const std::string &modClause);
  void genSmackCodeModifies(Program *program, const std::set<std::string> &bplGlobals);
  void addNewSCC(const std::string &procName);
  void dfs(ProcDecl *curProc);
  void genSCCs(Program *program);
  void genSCCGraph(Program *program);
  void addEdge(const CallStmt *callStmt, int parentSCC);
  void addIfGlobalVar(std::string exprName, const std::string &procName);
  void calcModifiesOfExprs(const std::list<const Expr*> exprs, const std::string &procName);
  void calcModifiesOfStmt(const Stmt *stmt, const std::string procName);
  void calcModifiesOfSCCs(Program *program);
  void propagateModifiesUpGraph();
  void addSmackGlobals(const std::set<std::string> &bplGlobals);
  void addModifies(Program *program);
  void genUserCodeModifies(Program *program, const std::set<std::string> &bplGlobals);

public:
  static char ID; // Pass identification, replacement for typeid

  GenModifies() : llvm::ModulePass(ID), maxIndex(1) {
    SCCGraph.push_back(std::set<int>());
    modVars.push_back(std::set<std::string>());
  }

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

