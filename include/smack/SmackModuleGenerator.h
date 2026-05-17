//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKMODULEGENERATOR_H
#define SMACKMODULEGENERATOR_H

#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace llvm {
class LoopInfo;
}

namespace smack {

class Program;
class Regions;
struct SmackMemoryPartitionReport;

class SmackModuleGenerator : public llvm::ModulePass {
private:
  Program *program;
  bool structuredBplLoops;
  bool structuredBplLoopsStrict;
  SmackMemoryPartitionReport *memoryPartitionReport;

public:
  static char ID; // Pass identification, replacement for typeid

  SmackModuleGenerator();
  SmackModuleGenerator(bool structuredBplLoops,
                       bool structuredBplLoopsStrict);
  SmackModuleGenerator(bool structuredBplLoops, bool structuredBplLoopsStrict,
                       SmackMemoryPartitionReport *memoryPartitionReport);
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
  virtual bool runOnModule(llvm::Module &m) override;
  void generateProgram(llvm::Module &m);
  // Variant for NewPM: caller supplies Regions + per-function LoopInfo getter
  // so we don't need the legacy Pass::getAnalysis machinery.
  void generateProgramImpl(
      llvm::Module &M, Regions &regions,
      llvm::function_ref<llvm::LoopInfo &(llvm::Function &)> getLoopInfo);
  Program *getProgram() { return program; }
};

// NewPM ModuleAnalysis returning the generated `Program*`. Consumed by
// BplPrinterNewPM / BplFilePrinterNewPM. Owns the Program for the lifetime
// of the cached result; consumer pointers stay valid while MAM caches.
class SmackModuleGeneratorAnalysis
    : public llvm::AnalysisInfoMixin<SmackModuleGeneratorAnalysis> {
  friend llvm::AnalysisInfoMixin<SmackModuleGeneratorAnalysis>;
  static llvm::AnalysisKey Key;
  SmackMemoryPartitionReport *memoryPartitionReport;

public:
  explicit SmackModuleGeneratorAnalysis(
      SmackMemoryPartitionReport *memoryPartitionReport = nullptr)
      : memoryPartitionReport(memoryPartitionReport) {}

  struct Result {
    // Holds the SmackModuleGenerator instance alive (which owns the Program).
    std::unique_ptr<SmackModuleGenerator> generator;
    Program *getProgram() { return generator->getProgram(); }
    bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                    llvm::ModuleAnalysisManager::Invalidator &) {
      return false; // sticky cache
    }
  };

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
};

} // namespace smack

#endif // SMACKMODULEGENERATOR_H
