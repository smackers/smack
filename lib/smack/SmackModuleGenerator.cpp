//
// This file is distributed under the MIT License. See LICENSE for details.
//
#define DEBUG_TYPE "smack-mod-gen"
#include "smack/SmackModuleGenerator.h"
#include "smack/BoogieAst.h"
#include "smack/DSAWrapper.h"
#include "smack/Debug.h"
#include "smack/Naming.h"
#include "smack/Prelude.h"
#include "smack/Regions.h"
#include "smack/SmackInstGenerator.h"
#include "smack/SmackOptions.h"
#include "smack/SmackRep.h"

#include <cctype>
#include <map>
#include <set>
#include <sstream>

namespace smack {

namespace {

using NameCounts = std::map<std::string, unsigned>;

bool isBoogieIdentifierChar(char c) {
  unsigned char uc = static_cast<unsigned char>(c);
  return std::isalnum(uc) || c == '_' || c == '.' || c == '$' || c == '#' ||
         c == '\'' || c == '~' || c == '^' || c == '?';
}

NameCounts countMemoryMapNames(const std::string &text) {
  NameCounts counts;
  const std::string prefix = Naming::MEMORY + ".";

  for (size_t pos = 0; (pos = text.find(prefix, pos)) != std::string::npos;) {
    size_t end = pos + prefix.size();
    if (text.compare(end, 2, "S.") == 0)
      end += 2;

    size_t digits = end;
    while (end < text.size() &&
           std::isdigit(static_cast<unsigned char>(text[end])))
      end++;

    if (end != digits &&
        (end == text.size() || !isBoogieIdentifierChar(text[end])))
      counts[text.substr(pos, end - pos)]++;

    pos += prefix.size();
  }
  return counts;
}

NameCounts countMemoryMapNames(const Stmt *stmt) {
  std::ostringstream os;
  stmt->print(os);
  return countMemoryMapNames(os.str());
}

void eliminateDeadStaticInitMaps(Program &program, SmackRep &rep) {
  std::map<const Stmt *, std::string> candidates;
  NameCounts initializerCounts;

  for (auto *decl : program) {
    auto *proc = dyn_cast<ProcDecl>(decl);
    if (!proc || proc->getName() != Naming::STATIC_INIT_PROC)
      continue;

    for (auto *block : proc->getBlocks()) {
      for (auto *stmt : block->getStatements()) {
        auto *assign = dyn_cast<AssignStmt>(stmt);
        if (!assign || assign->getLhs().size() != 1)
          continue;

        std::ostringstream lhs;
        assign->getLhs().front()->print(lhs);

        NameCounts names = countMemoryMapNames(stmt);
        if (names.size() != 1 || names.begin()->first != lhs.str())
          continue;

        candidates.emplace(stmt, lhs.str());
        initializerCounts[lhs.str()] += names.begin()->second;
      }
    }
  }

  if (candidates.empty())
    return;

  std::ostringstream os;
  program.print(os);
  NameCounts allCounts = countMemoryMapNames(os.str());
  std::set<std::string> deadMaps;
  for (const auto &entry : initializerCounts) {
    if (allCounts[entry.first] == entry.second)
      deadMaps.insert(entry.first);
  }

  if (deadMaps.empty())
    return;

  for (auto *decl : program) {
    auto *proc = dyn_cast<ProcDecl>(decl);
    if (!proc || proc->getName() != Naming::STATIC_INIT_PROC)
      continue;

    for (auto *block : proc->getBlocks()) {
      auto &statements = block->getStatements();
      statements.remove_if([&](const Stmt *stmt) {
        auto it = candidates.find(stmt);
        return it != candidates.end() && deadMaps.count(it->second) != 0;
      });
    }
  }

  for (const auto &name : deadMaps)
    rep.markDeadMemoryMap(name);

  SDEBUG(errs() << "Eliminated " << deadMaps.size()
                << " dead static-initializer memory maps.\n");
}

} // namespace

llvm::RegisterPass<SmackModuleGenerator> X("smack", "SMACK generator pass");
char SmackModuleGenerator::ID = 0;

SmackModuleGenerator::SmackModuleGenerator() : ModulePass(ID) {
  program = new Program();
}

void SmackModuleGenerator::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<llvm::LoopInfoWrapperPass>();
  AU.addRequired<DSAWrapper>();
  AU.addRequired<Regions>();
}

bool SmackModuleGenerator::runOnModule(llvm::Module &m) {
  generateProgram(m);
  return false;
}

void SmackModuleGenerator::generateProgram(llvm::Module &M) {

  Naming naming;
  SmackRep rep(&M.getDataLayout(), &naming, program, &getAnalysis<Regions>());
  std::list<Decl *> &decls = program->getDeclarations();

  SDEBUG(errs() << "Analyzing globals...\n");

  for (auto &G : M.globals()) {
    auto ds = rep.globalDecl(&G);
    decls.insert(decls.end(), ds.begin(), ds.end());
  }

  // Find the entry-point function for global memory map declarations.
  for (auto &F : M) {
    if (F.hasName() && SmackOptions::isEntryPoint(F.getName())) {
      rep.entryFunction = &F;
      break;
    }
  }

  SDEBUG(errs() << "Analyzing functions...\n");

  for (auto &F : M) {

    // Reset the counters for per-function names
    naming.reset();

    // Set the current function context for SmackRep.
    // Non-entry usesGlobalMemory functions (e.g., __SMACK_static_init) must
    // use the entry function's region context so that their $M.R references
    // match the global declarations (which use entry function's indices).
    if (rep.entryFunction && F.hasName() &&
        SmackOptions::usesGlobalMemory(F.getName()) &&
        !SmackOptions::isEntryPoint(F.getName())) {
      rep.currentFunction = rep.entryFunction;
      // Region probes for this body's values must be translated from its
      // own DSA graph into the entry function's graph (field-precise).
      getAnalysis<Regions>().setTranslationSource(&F);
    } else {
      rep.currentFunction = &F;
      getAnalysis<Regions>().setTranslationSource(nullptr);
    }

    SDEBUG(errs() << "Analyzing function: " << naming.get(F) << "\n");

    auto ds = rep.globalDecl(&F);
    decls.insert(decls.end(), ds.begin(), ds.end());

    auto procs = rep.procedure(&F);
    assert(procs.size() > 0);

    if (naming.get(F) != Naming::DECLARATIONS_PROC)
      decls.insert(decls.end(), procs.begin(), procs.end());

    if (F.isDeclaration())
      continue;

    if (!F.empty() && !F.getEntryBlock().empty()) {
      SDEBUG(errs() << "Analyzing function body: " << naming.get(F) << "\n");

      for (auto P : procs) {
        SmackInstGenerator igen(
            getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo(), &rep, P,
            &naming);
        SDEBUG(errs() << "Generating body for " << naming.get(F) << "\n");
        igen.visit(F);
        SDEBUG(errs() << "\n");

        // First execute static initializers, in the main procedure.
        if (F.hasName() && SmackOptions::isEntryPoint(F.getName())) {
          P->insert(Stmt::call(Naming::INITIALIZE_PROC));

        } else if (naming.get(F).find(Naming::INIT_FUNC_PREFIX) == 0)
          rep.addInitFunc(&F);

        // Add local memory variable declarations.
        if (F.hasName() && SmackOptions::isEntryPoint(F.getName())) {
          // Entry points: local vars for non-global-scope regions.
          unsigned numRegions = getAnalysis<Regions>().size(&F);
          for (unsigned r = 0; r < numRegions; r++) {
            if (!getAnalysis<Regions>().get(&F, r).isGlobalScope())
              P->getDeclarations().push_back(
                  Decl::variable(rep.memReg(r), rep.memType(&F, r)));
          }
        } else if (!(F.hasName() &&
                     SmackOptions::usesGlobalMemory(F.getName()))) {
          // Regular functions: local shadows for private regions only;
          // memory bound to module-level maps (entry or shared) is
          // accessed directly.
          auto &gm = getAnalysis<Regions>().getGlobalMemoryMapping(&F);
          auto accessed = getAnalysis<Regions>().getAccessedRegions(&F);
          for (unsigned r : accessed) {
            if (gm.count(r) ||
                getAnalysis<Regions>().getSharedRegionIndex(&F, r) >= 0)
              continue;
            P->getDeclarations().push_back(
                Decl::variable(rep.memPath(r), rep.memType(&F, r)));
          }
        }
      }
      SDEBUG(errs() << "Finished analyzing function: " << naming.get(F)
                    << "\n\n");
    }

    // No explicit modifies clauses for global-memory procedures;
    // the verifier infers them automatically.
  }

  auto ds = rep.auxiliaryDeclarations();
  decls.insert(decls.end(), ds.begin(), ds.end());
  decls.insert(decls.end(), rep.getInitFuncs());

  if (getAnalysis<DSAWrapper>().isContextSensitive())
    eliminateDeadStaticInitMaps(*program, rep);

  // NOTE we must do this after instruction generation, since we would not
  // otherwise know how many regions to declare.
  Prelude prelude(rep);
  program->appendPrelude(prelude.getPrelude());

  std::list<Decl *> kill_list;
  for (auto D : *program) {
    if (auto P = dyn_cast<ProcDecl>(D)) {
      if (rep.isContractExpr(D->getName())) {
        decls.insert(decls.end(), Decl::code(P));
        kill_list.push_back(P);
      }
    }
  }
  for (auto D : kill_list)
    decls.erase(std::remove(decls.begin(), decls.end(), D), decls.end());
}

} // namespace smack
