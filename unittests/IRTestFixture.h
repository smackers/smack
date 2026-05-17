//
// This file is distributed under the MIT License. See LICENSE for details.
//
// Lightweight gtest fixture for unit tests that need a real
// llvm::Module. Subclass IRTestFixture and call parseIR("<assembly>")
// to get a hand-authored Module + LLVMContext pair.
//
// Use this for pass-level tests that operate purely on a Module —
// callers, GEP shape walking, instruction visitors, naming. For tests
// that need the full SMACK pipeline (Regions + sea-dsa), prefer the
// end-to-end regtest matrix instead.
//

#ifndef SMACK_IR_TEST_FIXTURE_H
#define SMACK_IR_TEST_FIXTURE_H

#include "llvm/AsmParser/Parser.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/SourceMgr.h"
#include "gtest/gtest.h"

#include <memory>
#include <string>

namespace smack {
namespace test {

class IRTestFixture : public ::testing::Test {
public:
  // Parse the supplied LLVM textual IR + leave the Module accessible
  // via member `M`. On parse failure, asserts and prints the diagnostic.
  void parseIR(const std::string &ir) {
    llvm::SMDiagnostic err;
    M = llvm::parseAssemblyString(ir, err, ctx);
    if (!M) {
      std::string msg;
      llvm::raw_string_ostream os(msg);
      err.print("test", os);
      FAIL() << "parseAssemblyString failed:\n" << msg;
    }
  }

  llvm::LLVMContext ctx;
  std::unique_ptr<llvm::Module> M;
};

} // namespace test
} // namespace smack

#endif // SMACK_IR_TEST_FIXTURE_H
