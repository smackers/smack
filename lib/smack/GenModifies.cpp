//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/GenModifies.h"
#include "smack/SmackRep.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GraphWriter.h"
#include <sstream>
#include <iostream>
#include <string>
#include <vector>
#include <set>
#include <map>
#include <regex>
#include <algorithm>

namespace smack {

using llvm::errs;

char GenModifies::ID = 0;

void GenModifies::genSCC(ProcDecl *curProc) {
  std::string name = curProc->getName();
  st.push(name);
  onStack[name] = true;
  index[name] = maxIndex;
  low[name] = maxIndex++;
  for (Block *block : *curProc) {
    for (const Stmt *stmt : *block) {
      if (stmt->getKind() == 5) {
        std::string next = ((CallStmt*)stmt)->getName();
        if (proc.count(next) && !index[next]) {
          genSCC(proc[next]);
          low[name] = std::min(low[name], low[next]);
        } else if (onStack[next]) {
          low[name] = std::min(low[name], index[next]);
        }
      }
    }
  }
  if (low[name] == index[name]) {
    std::string toAdd;
    do {
      toAdd = st.top();
      st.pop();
      onStack[toAdd] = false;
      SCCOfProc[toAdd] = modVars.size();
    } while (toAdd != name);
    modVars.push_back(std::set<std::string>());
    SCCGraph.push_back(std::set<int>());
  }
}

void GenModifies::genSCCGraph(ProcDecl *curProc)
{
  int curSCC = SCCOfProc[curProc->getName()];
  for (Block *block : *curProc) {
    for (const Stmt *stmt : *block) {
      if (stmt->getKind() == 5) {
        std::string next = ((CallStmt*)stmt)->getName();
        int childSCC = SCCOfProc[next];
        if (childSCC && childSCC != curSCC) {
          SCCGraph[childSCC].insert(curSCC);
        }
      }
    }
  }
}

void GenModifies::calcModifies(ProcDecl *curProc) {
  Regex GLOBAL_VAR("\\$M.[[:digit:]]+");
  for (Block *block : *curProc) {
    for (const Stmt *stmt : *block) {
      if (stmt->getKind() == 2) {
        AssignStmt *assignStmt = (AssignStmt*)stmt;
        std::list<const Expr*> lhs = assignStmt->getlhs();
        for (auto expr : lhs) {
          const VarExpr *vExpr = dyn_cast<VarExpr>(expr);
          if (vExpr) {
            std::string name = vExpr->name();
            if (GLOBAL_VAR.match(name)) {
              std::string var = GLOBAL_VAR.sub("\\0", name);  
              modVars[SCCOfProc[curProc->getName()]].insert(var);
            }
          }
        }
        std::list<const Expr*> rhs = assignStmt->getrhs();
        for (auto expr : rhs) {
          const FunExpr *fExpr = dyn_cast<FunExpr>(expr);
          if (fExpr) {
            std::list<const Expr*> args = fExpr->getArgs();
            for (auto expr : args) {
              const VarExpr *vExpr = dyn_cast<VarExpr>(expr);
              if (vExpr) {
                std::string name = vExpr->name();
                if (GLOBAL_VAR.match(name)) {
                  std::string var = GLOBAL_VAR.sub("\\0", name);  
                  modVars[SCCOfProc[curProc->getName()]].insert(var);
                }
              }
            }
          }
        }
      } else if (stmt->getKind() == 5) {
        CallStmt *callStmt = (CallStmt*)stmt;
        std::list<std::string> returns = callStmt->getReturns();
        for (const auto &name : returns) {
          if (GLOBAL_VAR.match(name)) {
            std::string var = GLOBAL_VAR.sub("\\0", name);
            modVars[SCCOfProc[curProc->getName()]].insert(var);
          }
        }
        std::list<const Expr*> params = callStmt->getParams();
        for (auto expr : params) {
          const VarExpr *vExpr = dyn_cast<VarExpr>(expr);
          if (vExpr) {
            std::string name = vExpr->name();
            if (GLOBAL_VAR.match(name)) {
              std::string var = GLOBAL_VAR.sub("\\0", name);
              modVars[SCCOfProc[curProc->getName()]].insert(var);
            }
          }
        }
      }
    }
  }
}

bool GenModifies::runOnModule(llvm::Module& m) {
  SmackModuleGenerator& smackGenerator = getAnalysis<SmackModuleGenerator>();
  Program& program = smackGenerator.getProgram();
  std::set<std::string> bplGlobals = smackGenerator.getBplGlobals();
  modVars.push_back(std::set<std::string>());
  SCCGraph.push_back(std::set<int>());
  std::string nameRegex = "[[:alpha:]_.$#'`^\?][[:alnum:]_.$#'`^\?]*";
  Regex PROC_DECL("^([[:space:]]*procedure(.|[[:space:]])*[[:space:]]+(" + nameRegex + ")[[:space:]]*\\((.|[[:space:]])*\\)(.|[[:space:]])*)(\\{(.|[[:space:]])*\\})");
  Regex MOD_CL("modifies[[:space:]]+" + nameRegex + "([[:space:]]*,[[:space:]]*" + nameRegex + ")*;"); 
  for (Decl *&decl : program) {
    if (decl->getKind() == 2) {
      proc[decl->getName()] = (ProcDecl*)decl;
    } else if (decl->getKind() == 6 && !bplGlobals.empty()) {
      std::string str = decl->getName();
      if (PROC_DECL.match(str) && !MOD_CL.match(str)) {
        std::string modStr = "\nmodifies";
        for (std::string var : bplGlobals) {
          modStr += " " + var + ",";
        }
        modStr[modStr.size() - 1] = ';';
        modStr.push_back('\n');
        std::string newStr = PROC_DECL.sub("\\1", str) + modStr + PROC_DECL.sub("\\6", str);
        decl = Decl::code(newStr, newStr);
      }
    }
  }
  for (Decl *decl : program) {
    if (decl->getKind() == 2 && !index[decl->getName()]) {
      genSCC((ProcDecl*)decl);
    }
  }
  for (Decl *decl : program) {
    if (decl->getKind() == 2) {
      genSCCGraph((ProcDecl*)decl);
    }
  }
  for (Decl *decl : program) {
    if (decl->getKind() == 2) {
      calcModifies((ProcDecl*)decl);
    }
  }
  for (size_t child = 1; child < SCCGraph.size(); ++child) {
    for (int parent : SCCGraph[child]) {
      modVars[parent].insert(modVars[child].begin(), modVars[child].end());
    }
  }
  for (size_t scc = 0; scc < modVars.size(); ++scc) {
    modVars[scc].insert(bplGlobals.begin(), bplGlobals.end());
  }
  for (Decl *decl : program) {
    if (decl->getKind() == 2 && ((ProcDecl*)decl)->begin() != ((ProcDecl*)decl)->end()) {
      int index = SCCOfProc[decl->getName()];
      std::list<std::string> &modList = ((ProcDecl*)decl)->getModifies();
      modList.insert(modList.end(), modVars[index].begin(), modVars[index].end());
    }
  }
  // DEBUG_WITH_TYPE("bpl", errs() << "" << s.str());
  return false;
}
}
