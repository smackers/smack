//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/GenModifies.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GraphWriter.h"
#include <list>
#include <algorithm>
#include <iterator>

namespace smack {

using llvm::errs;
using llvm::dyn_cast;
using llvm::isa;

char GenModifies::ID = 0;

void GenModifies::initProcMap(Program *program) {
  for (Decl *decl : *program) {
    if (ProcDecl *procDecl = dyn_cast<ProcDecl>(decl)) {
      proc[procDecl->getName()] = procDecl;
    }
  }
}

void GenModifies::insertModifiesClause(Decl *&decl, Regex &PROC_DECL, const std::set<std::string> &bplGlobals) {
  std::string modStr = "\nmodifies";

  for (std::string var : bplGlobals) {
    modStr += " " + var + ",";
  }

  modStr[modStr.size() - 1] = ';';
  modStr.push_back('\n');

  std::string newStr = PROC_DECL.sub("\\1", decl->getName()) + modStr + PROC_DECL.sub("\\6", decl->getName());

  decl = Decl::code(newStr, newStr);
}

void GenModifies::genSmackCodeModifies(Program *program, const std::set<std::string> &bplGlobals) {
  const std::string NAME_REGEX = "[[:alpha:]_.$#'`^\?][[:alnum:]_.$#'`^\?]*";
  Regex PROC_DECL("^([[:space:]]*procedure(.|[[:space:]])*[[:space:]]+(" + NAME_REGEX + ")[[:space:]]*\\((.|[[:space:]])*\\)(.|[[:space:]])*)(\\{(.|[[:space:]])*\\})");
  Regex MOD_CL("modifies[[:space:]]+" + NAME_REGEX + "([[:space:]]*,[[:space:]]*" + NAME_REGEX + ")*;"); 

  for (Decl *&decl : *program) {
    if (isa<CodeDecl>(decl)) {
      if (!bplGlobals.empty()) {
        if (PROC_DECL.match(decl->getName()) && !MOD_CL.match(decl->getName())) {
          insertModifiesClause(decl, PROC_DECL, bplGlobals);
        }
      }
    }
  }
}

void GenModifies::addNewSCC(const std::string &procName) {
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

void GenModifies::dfs(ProcDecl *procDecl) {
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

void GenModifies::genSCCs(Program *program) {
  for (Decl *decl : *program) {
    if (ProcDecl *procDecl = dyn_cast<ProcDecl>(decl)) {
      if (!index[procDecl->getName()]) {
        dfs(procDecl);
      }
    }
  }
}

void GenModifies::addEdge(const CallStmt *callStmt, int parentSCC) {
  int childSCC = SCCOfProc[callStmt->getName()];

  if (childSCC && childSCC != parentSCC) {
    SCCGraph[childSCC].insert(parentSCC);
  }
}

void GenModifies::genSCCGraph(Program *program) {
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

void GenModifies::addIfGlobalVar(const std::string exprName, const std::string &procName) {
  static Regex GLOBAL_VAR("\\$M.[[:digit:]]+");
  if (GLOBAL_VAR.match(exprName)) {
    std::string var = GLOBAL_VAR.sub("\\0", exprName);  

    modVars[SCCOfProc[procName]].insert(var);
  }
}

void GenModifies::calcModifiesOfExprs(const std::list<const Expr*> exprs, const std::string &procName) {
  for (auto expr : exprs) {
    if (const VarExpr *varExpr = dyn_cast<VarExpr>(expr)) {
      addIfGlobalVar(varExpr->name(), procName);
    }
  }
}

void GenModifies::calcModifiesOfStmt(const Stmt *stmt, const std::string procName) {
  if (const AssignStmt* assignStmt = dyn_cast<AssignStmt>(stmt)) {
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

void GenModifies::calcModifiesOfSCCs(Program *program) {
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

void GenModifies::propagateModifiesUpGraph() {
  for (size_t child = 1; child < SCCGraph.size(); ++child) {
    for (int parent : SCCGraph[child]) {
      modVars[parent].insert(modVars[child].begin(), modVars[child].end());
    }
  }
}

void GenModifies::addSmackGlobals(const std::set<std::string> &bplGlobals) {
  for (size_t scc = 0; scc < modVars.size(); ++scc) {
    modVars[scc].insert(bplGlobals.begin(), bplGlobals.end());
  }
}

void GenModifies::addModifies(Program *program) {
  for (Decl *decl : *program) {
    if (ProcDecl *procDecl = dyn_cast<ProcDecl>(decl)) {
      if (procDecl->begin() != procDecl->end()) {
        int index = SCCOfProc[procDecl->getName()];

        std::list<std::string> &modList = procDecl->getModifies();

        modList.insert(modList.end(), modVars[index].begin(), modVars[index].end());
      }
    }
  }
}

void GenModifies::genUserCodeModifies(Program *program, const std::set<std::string> &bplGlobals) {
  genSCCs(program);

  calcModifiesOfSCCs(program);

  genSCCGraph(program);

  propagateModifiesUpGraph();

  addSmackGlobals(bplGlobals);

  addModifies(program);
}

bool GenModifies::runOnModule(llvm::Module& m) {
  SmackModuleGenerator &smackGenerator = getAnalysis<SmackModuleGenerator>();
  Program *program = smackGenerator.getProgram();

  std::set<std::string> bplGlobals;
  std::vector<std::string> oldBplGlobals = smackGenerator.getBplGlobals();
  std::copy(oldBplGlobals.begin(), oldBplGlobals.end(), std::inserter(bplGlobals, bplGlobals.end()));

  initProcMap(program);

  genSmackCodeModifies(program, bplGlobals);

  genUserCodeModifies(program, bplGlobals);

  // DEBUG_WITH_TYPE("bpl", errs() << "" << s.str());
  return false;
}
}
