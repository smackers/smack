#include "ExternalizePass.h"

#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/ToolOutputFile.h"

static llvm::cl::opt<std::string>
    InputFilename("in", llvm::cl::desc("Input bitcode filename"),
                  llvm::cl::Required, llvm::cl::value_desc("input filename"));

static llvm::cl::opt<std::string>
    OutputFilename("out", llvm::cl::desc("Output bitcode filename"),
                   llvm::cl::Required, llvm::cl::value_desc("output filename"));

int main(int argc, char **argv) {

  llvm::llvm_shutdown_obj shutdown; // calls llvm_shutdown() on exit
  llvm::cl::ParseCommandLineOptions(
      argc, argv, "extern-statics - Externalize static functions\n");

  llvm::sys::PrintStackTraceOnErrorSignal(argv[0]);
  llvm::PrettyStackTraceProgram PSTP(argc, argv);
  llvm::EnableDebugBuffering = true;

  llvm::SMDiagnostic err;
  llvm::LLVMContext Context;

  std::unique_ptr<llvm::Module> module =
      llvm::parseIRFile(InputFilename, err, Context);
  if (!err.getMessage().empty()) {
    llvm::errs() << "Problem reading input bitcode/IR: " +
                        err.getMessage().str()
                 << "\n";
    return 1;
  }

  ///////////////////////////////
  // initialise and run passes //
  ///////////////////////////////

  llvm::legacy::PassManager pass_manager;
  pass_manager.add(new externalize::ExternalizePass());

  pass_manager.run(*module.get());

  std::error_code EC;
  auto out = new llvm::ToolOutputFile(OutputFilename.c_str(), EC,
                                      llvm::sys::fs::F_None);

  if (EC) {
    llvm::errs() << "Could not create output file: " << EC.message() << "\n";
    return 1;
  }
  out->keep();

  WriteBitcodeToFile(*module, out->os());

  delete out;

  return 0;
}
