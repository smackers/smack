//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/raw_ostream.h"

#include "smack/DiffProductMatcher.h"
#include "smack/SmackOptions.h"
#include "smack/SmackPipeline.h"

#include <memory>
#include <string>

using namespace llvm;

static cl::opt<std::string>
    LeftBitcode("left-bc", cl::desc("Left LLVM bitcode/IR input"),
                cl::Required, cl::value_desc("filename"));

static cl::opt<std::string>
    RightBitcode("right-bc", cl::desc("Right LLVM bitcode/IR input"),
                 cl::Required, cl::value_desc("filename"));

static cl::opt<std::string>
    LeftEntry("left-entry", cl::desc("Left entry function"), cl::Required,
              cl::value_desc("function"));

static cl::opt<std::string>
    RightEntry("right-entry", cl::desc("Right entry function"), cl::Required,
               cl::value_desc("function"));

static cl::opt<std::string>
    LeftBpl("left-bpl", cl::desc("Left Boogie output"), cl::Required,
            cl::value_desc("filename"));

static cl::opt<std::string>
    RightBpl("right-bpl", cl::desc("Right Boogie output"), cl::Required,
             cl::value_desc("filename"));

static cl::opt<std::string>
    MatchJson("match-json", cl::desc("LLVM structural match JSON output"),
              cl::Required, cl::value_desc("filename"));

static cl::opt<std::string>
    LeftLl("left-ll", cl::desc("Optional normalized left LLVM IR dump"),
           cl::init(""), cl::value_desc("filename"));

static cl::opt<std::string>
    RightLl("right-ll", cl::desc("Optional normalized right LLVM IR dump"),
            cl::init(""), cl::value_desc("filename"));

static cl::opt<bool> StaticUnroll(
    "static-unroll",
    cl::desc("Use LLVM to statically unroll loops when possible"),
    cl::init(false));

static cl::opt<std::string>
    DefaultDataLayout("default-data-layout",
                      cl::desc("data layout string to use if not specified by "
                               "module"),
                      cl::init(""), cl::value_desc("layout-string"));

static cl::opt<bool> Modular(
    "modular",
    cl::desc("Enable contracts-based modular deductive verification"),
    cl::init(false));

static cl::opt<bool> StructuredBplLoops(
    "structured-bpl-loops",
    cl::desc("For functional-equivalence product lowering, emit supported "
             "LLVM natural loops as structured Boogie while statements"),
    cl::init(false));

static cl::opt<bool> StructuredBplLoopsStrict(
    "structured-bpl-loops-strict",
    cl::desc("Fail paired product lowering if structured Boogie loop emission "
             "cannot structure every detected LLVM loop"),
    cl::init(false));

namespace {

void check(std::string E) {
  if (!E.empty()) {
    if (errs().has_colors())
      errs().changeColor(raw_ostream::RED);
    errs() << E << "\n";
    if (errs().has_colors())
      errs().resetColor();
    exit(1);
  }
}

std::unique_ptr<Module> readModule(const std::string &filename,
                                   LLVMContext &context) {
  SMDiagnostic err;
  std::unique_ptr<Module> module = parseIRFile(filename, err, context);
  if (!err.getMessage().empty())
    check("Problem reading input bitcode/IR " + filename + ": " +
          err.getMessage().str());
  if (!module)
    check("Problem reading input bitcode/IR " + filename);
  return module;
}

void writeModuleLl(Module &module, const std::string &filename) {
  if (filename.empty())
    return;
  std::error_code EC;
  ToolOutputFile F(filename.c_str(), EC, sys::fs::OF_None);
  if (EC)
    check(EC.message());
  module.print(F.os(), nullptr);
  F.keep();
}

void writeBpl(Module &module, const std::string &filename,
              const smack::SmackBplOptions &options) {
  std::error_code EC;
  ToolOutputFile F(filename.c_str(), EC, sys::fs::OF_None);
  if (EC)
    check(EC.message());
  smack::emitSmackBpl(module, F.os(), options);
  F.keep();
}

void writeText(const std::string &filename, const std::string &text) {
  std::error_code EC;
  ToolOutputFile F(filename.c_str(), EC, sys::fs::OF_Text);
  if (EC)
    check(EC.message());
  F.os() << text;
  F.keep();
}

} // namespace

int main(int argc, char **argv) {
  llvm_shutdown_obj shutdown;
  cl::ParseCommandLineOptions(
      argc, argv,
      "llvm-diffmatch2bpl - paired LLVM-to-Boogie diff-product lowering\n");

  sys::PrintStackTraceOnErrorSignal(argv[0]);
  PrettyStackTraceProgram PSTP(argc, argv);
  EnableDebugBuffering = true;

  InitializeAllTargets();
  InitializeAllTargetMCs();
  InitializeAllAsmPrinters();
  InitializeAllAsmParsers();

  LLVMContext leftContext;
  LLVMContext rightContext;
  std::unique_ptr<Module> leftModule = readModule(LeftBitcode, leftContext);
  std::unique_ptr<Module> rightModule = readModule(RightBitcode, rightContext);

  smack::SmackPipelineOptions options;
  options.staticUnroll = StaticUnroll;
  options.modular = Modular;
  options.defaultDataLayout = DefaultDataLayout;
  // Force-link SmackOptions so llvm-diffmatch2bpl exposes the same low-level
  // flags as llvm2bpl.
  (void)smack::SmackOptions::NoMemoryRegionSplitting.getValue();

  smack::runSmackPreBplPipeline(*leftModule, options);
  smack::runSmackPreBplPipeline(*rightModule, options);

  std::string matchJson = smack::buildDiffProductMatchJson(
      *leftModule, *rightModule, LeftEntry, RightEntry);
  writeText(MatchJson, matchJson);

  writeModuleLl(*leftModule, LeftLl);
  writeModuleLl(*rightModule, RightLl);
  smack::SmackBplOptions bplOptions;
  bplOptions.structuredLoops = StructuredBplLoops || StructuredBplLoopsStrict;
  bplOptions.structuredLoopsStrict = StructuredBplLoopsStrict;
  writeBpl(*leftModule, LeftBpl, bplOptions);
  writeBpl(*rightModule, RightBpl, bplOptions);

  return 0;
}
