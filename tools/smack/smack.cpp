// 
// Copyright (c) 2013 Pantazis Deligiannis (p.deligiannis@imperial.ac.uk)
// This file is distributed under the MIT License. See LICENSE for details.
// 

#include "llvm/LinkAllPasses.h"
#include "llvm/PassManager.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/raw_ostream.h"

#include "smack/BplFilePrinter.h"
#include "smack/DSAAliasAnalysis.h"
#include "smack/SmackModuleGenerator.h"
#include "assistDS/StructReturnToPointer.h"
#include "assistDS/SimplifyExtractValue.h"
#include "assistDS/SimplifyInsertValue.h"

static llvm::cl::opt<std::string>
InputFilename(llvm::cl::Positional, llvm::cl::desc("<input LLVM bitcode file>"),
  llvm::cl::Required, llvm::cl::value_desc("filename"));

static llvm::cl::opt<std::string>
OutputFilename("o", llvm::cl::desc("Override output filename"),
  llvm::cl::init(""), llvm::cl::value_desc("filename"));

static llvm::cl::opt<std::string>
DefaultDataLayout("default-data-layout", llvm::cl::desc("data layout string to use if not specified by module"),
  llvm::cl::init(""), llvm::cl::value_desc("layout-string"));

// removes extension from filename if there is one
std::string getFileName(const std::string &str) {
  std::string filename = str;
  size_t lastdot = str.find_last_of(".");
  if (lastdot != std::string::npos)
    filename = str.substr(0, lastdot);  
  return filename; 
}

int main(int argc, char **argv) {
  llvm::llvm_shutdown_obj shutdown;  // calls llvm_shutdown() on exit
  llvm::cl::ParseCommandLineOptions(argc, argv, "SMACK - LLVM bitcode to Boogie transformation\n");

  llvm::sys::PrintStackTraceOnErrorSignal();
  llvm::PrettyStackTraceProgram PSTP(argc, argv);
  llvm::EnableDebugBuffering = true;

  if (OutputFilename.empty()) {
//    OutputFilename = getFileName(InputFilename) + ".bpl";
    OutputFilename = "a.bpl";
  }
 
  std::string error_msg;
  llvm::SMDiagnostic err;
  llvm::LLVMContext &context = llvm::getGlobalContext();  
  std::unique_ptr<llvm::Module> module;
  std::unique_ptr<llvm::tool_output_file> output;
 
  module.reset(llvm::ParseIRFile(InputFilename, err, context));
  if (module.get() == 0) {
    if (llvm::errs().has_colors()) llvm::errs().changeColor(llvm::raw_ostream::RED);
    llvm::errs() << "error: " << "Bitcode was not properly read; " << err.getMessage() << "\n";
    if (llvm::errs().has_colors()) llvm::errs().resetColor();
    return 1;
  }
 
  output.reset(new llvm::tool_output_file(OutputFilename.c_str(), error_msg, llvm::sys::fs::F_None));
  if (!error_msg.empty()) {
    if (llvm::errs().has_colors()) llvm::errs().changeColor(llvm::raw_ostream::RED);
    llvm::errs() << "error: " << error_msg << "\n";
    if (llvm::errs().has_colors()) llvm::errs().resetColor();
    return 1;
  }
 
  ///////////////////////////////
  // initialise and run passes //
  ///////////////////////////////

  llvm::PassManager pass_manager;
  llvm::PassRegistry &Registry = *llvm::PassRegistry::getPassRegistry();
  llvm::initializeAnalysis(Registry);
 
  // add an appropriate DataLayout instance for the module
  const llvm::DataLayout *dl = 0;
  const std::string &moduleDataLayout = module.get()->getDataLayoutStr();
  if (!moduleDataLayout.empty())
    dl = new llvm::DataLayout(moduleDataLayout);
  else if (!DefaultDataLayout.empty())
    dl = new llvm::DataLayout(moduleDataLayout);
  if (dl) pass_manager.add(new llvm::DataLayoutPass(*dl));

  pass_manager.add(llvm::createLowerSwitchPass());
  pass_manager.add(llvm::createCFGSimplificationPass());
  pass_manager.add(llvm::createInternalizePass());
  pass_manager.add(llvm::createPromoteMemoryToRegisterPass());
  pass_manager.add(new llvm::StructRet());
  pass_manager.add(new llvm::SimplifyEV());
  pass_manager.add(new llvm::SimplifyIV());
  pass_manager.add(new smack::SmackModuleGenerator());
  pass_manager.add(new smack::BplFilePrinter(output->os()));
  pass_manager.run(*module.get());

  output->keep();

  return 0;
}

