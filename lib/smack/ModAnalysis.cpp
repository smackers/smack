//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/ModAnalysis.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GraphWriter.h"
#include <algorithm>
#include <iterator>
#include <list>

namespace smack {

using llvm::errs;
using llvm::dyn_cast;
using llvm::isa;

char ModAnalysis::ID = 0;

void ModAnalysis::initProcMap(Program *program) {
  for (Decl *decl : *program) {
    if (ProcDecl *procDecl = dyn_cast<ProcDecl>(decl)) {
      proc[procDecl->getName()] = procDecl;
    }
  }
}

std::string ModAnalysis::getBplGlobalsModifiesClause(
    const std::set<std::string> &bplGlobals) {
  std::string modClause = "\nmodifies";

  for (std::string var : bplGlobals) {
    modClause += " " + var + ",";
  }

  modClause[modClause.size() - 1] = ';';
  modClause.push_back('\n');

  return modClause;
}

void ModAnalysis::fixPrelude(Program *program, const std::string &modClause) {
  std::string searchStr = "procedure $global_allocations()\n";
  std::string &prelude = program->getPrelude();
  size_t pos = prelude.find(searchStr);

  if (pos != std::string::npos) {
    std::string str1 = prelude.substr(0, pos + searchStr.size());
    std::string str2 = prelude.substr(pos + searchStr.size());
    prelude = str1 + modClause + str2;
  }
}

void ModAnalysis::addModifiesToSmackProcs(Program *program,
                                          const std::string &modClause) {
  const std::string NAME_REGEX = "[[:alpha:]_.$#'`^\?][[:alnum:]_.$#'`^\?]*";
  Regex PROC_DECL("^([[:space:]]*procedure[[:space:]]+[^\\(]*(" + NAME_REGEX +
                  ")[[:space:]]*\\([^\\)]*\\)[^\\{]*)(\\{(.|[[:space:]])*(\\}[["
                  ":space:]]*)$)");
  Regex MOD_CL("modifies[[:space:]]+" + NAME_REGEX +
               "([[:space:]]*,[[:space:]]*" + NAME_REGEX + ")*;");

  for (Decl *&decl : *program) {
    if (isa<CodeDecl>(decl)) {
      if (PROC_DECL.match(decl->getName()) && !MOD_CL.match(decl->getName())) {
        std::string newStr = PROC_DECL.sub("\\1", decl->getName()) + modClause +
                             PROC_DECL.sub("\\3", decl->getName());
        decl = Decl::code(newStr, newStr);
      }
    }
  }
}

void ModAnalysis::genSmackCodeModifies(
    Program *program, const std::set<std::string> &bplGlobals) {
  std::string modClause = getBplGlobalsModifiesClause(bplGlobals);
  fixPrelude(program, modClause);
  addModifiesToSmackProcs(program, modClause);
}

void ModAnalysis::addNewSCC(const std::string &procName) {
  std::string toAdd;

  do {
    toAdd = st.top();
    st.pop();
    onStack[toAdd] = false;
    SCCOfProc[toAdd] = modVars.size();
  } while (toAdd != procName);

  modVars.push_back(std::set<std::string>());
  SCCGraph.push_back(std::set<int>());
}

void ModAnalysis::dfs(ProcDecl *procDecl) {
  const std::string name = procDecl->getName();

  st.push(name);
  onStack[name] = true;
  index[name] = maxIndex;
  low[name] = maxIndex++;

  for (Block *block : *procDecl) {
    for (const Stmt *stmt : *block) {
      if (const CallStmt *callStmt = dyn_cast<CallStmt>(stmt)) {
        const std::string next = callStmt->getName();

        if (proc.count(next) && !index[next]) {
          dfs(proc[next]);
          low[name] = std::min(low[name], low[next]);
        } else if (onStack[next]) {
          low[name] = std::min(low[name], index[next]);
        }
      }
    }
  }

  if (low[name] == index[name]) {
    addNewSCC(name);
  }
}

void ModAnalysis::genSCCs(Program *program) {
  for (Decl *decl : *program) {
    if (ProcDecl *procDecl = dyn_cast<ProcDecl>(decl)) {
      if (!index[procDecl->getName()]) {
        dfs(procDecl);
      }
    }
  }
}

void ModAnalysis::addEdge(const CallStmt *callStmt, int parentSCC) {
  int childSCC = SCCOfProc[callStmt->getName()];

  if (childSCC && childSCC != parentSCC) {
    SCCGraph[childSCC].insert(parentSCC);
  }
}

void ModAnalysis::genSCCGraph(Program *program) {
  for (Decl *decl : *program) {
    if (ProcDecl *procDecl = dyn_cast<ProcDecl>(decl)) {
      int curSCC = SCCOfProc[procDecl->getName()];

      for (Block *block : *procDecl) {
        for (const Stmt *stmt : *block) {
          if (const CallStmt *callStmt = dyn_cast<CallStmt>(stmt)) {
            addEdge(callStmt, curSCC);
          }
        }
      }
    }
  }
}

void ModAnalysis::addIfGlobalVar(const std::string exprName,
                                 const std::string &procName) {
  static Regex GLOBAL_VAR("\\$M.[[:digit:]]+");
  if (GLOBAL_VAR.match(exprName)) {
    std::string var = GLOBAL_VAR.sub("\\0", exprName);

    modVars[SCCOfProc[procName]].insert(var);
  }
}

void ModAnalysis::calcModifiesOfExprs(const std::list<const Expr *> exprs,
                                      const std::string &procName) {
  for (auto expr : exprs) {
    if (const VarExpr *varExpr = dyn_cast<VarExpr>(expr)) {
      addIfGlobalVar(varExpr->name(), procName);
    }
  }
}

void ModAnalysis::calcModifiesOfStmt(const Stmt *stmt,
                                     const std::string procName) {
  if (const AssignStmt *assignStmt = dyn_cast<AssignStmt>(stmt)) {
    calcModifiesOfExprs(assignStmt->getlhs(), procName);

    for (const Expr *expr : assignStmt->getrhs()) {
      if (const FunExpr *funExpr = dyn_cast<FunExpr>(expr)) {
        calcModifiesOfExprs(funExpr->getArgs(), procName);
      }
    }
  } else if (const CallStmt *callStmt = dyn_cast<CallStmt>(stmt)) {
    for (const std::string retName : callStmt->getReturns()) {
      addIfGlobalVar(retName, procName);
    }

    calcModifiesOfExprs(callStmt->getParams(), procName);
  }
}

void ModAnalysis::calcModifiesOfSCCs(Program *program) {
  for (Decl *decl : *program) {
    if (ProcDecl *procDecl = dyn_cast<ProcDecl>(decl)) {
      for (Block *block : *procDecl) {
        for (const Stmt *stmt : *block) {
          calcModifiesOfStmt(stmt, procDecl->getName());
        }
      }
    }
  }
}

void ModAnalysis::propagateModifiesUpGraph() {
  for (size_t child = 1; child < SCCGraph.size(); ++child) {
    for (int parent : SCCGraph[child]) {
      modVars[parent].insert(modVars[child].begin(), modVars[child].end());
    }
  }
}

void ModAnalysis::addSmackGlobals(const std::set<std::string> &bplGlobals) {
  for (size_t scc = 0; scc < modVars.size(); ++scc) {
    modVars[scc].insert(bplGlobals.begin(), bplGlobals.end());
  }
}

void ModAnalysis::addModifies(Program *program) {
  for (Decl *decl : *program) {
    if (ProcDecl *procDecl = dyn_cast<ProcDecl>(decl)) {
      if (procDecl->begin() != procDecl->end()) {
        int index = SCCOfProc[procDecl->getName()];
        std::list<std::string> &modList = procDecl->getModifies();
        modList.insert(modList.end(), modVars[index].begin(),
                       modVars[index].end());
      }
    }
  }
}

void ModAnalysis::genUserCodeModifies(Program *program,
                                      const std::set<std::string> &bplGlobals) {
  genSCCs(program);
  calcModifiesOfSCCs(program);
  genSCCGraph(program);
  propagateModifiesUpGraph();
  addSmackGlobals(bplGlobals);
  addModifies(program);
}

bool ModAnalysis::runOnModule(llvm::Module &m) {
  SmackModuleGenerator &smackGenerator = getAnalysis<SmackModuleGenerator>();
  Program *program = smackGenerator.getProgram();

  std::set<std::string> bplGlobals;
  std::vector<std::string> oldBplGlobals = smackGenerator.getBplGlobals();
  std::copy(oldBplGlobals.begin(), oldBplGlobals.end(),
            std::inserter(bplGlobals, bplGlobals.end()));

  initProcMap(program);

  if (!bplGlobals.empty()) {
    genSmackCodeModifies(program, bplGlobals);
  }

  genUserCodeModifies(program, bplGlobals);

  // DEBUG_WITH_TYPE("bpl", errs() << "" << s.str());
  return false;
}
}
