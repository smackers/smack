//
// This file is distributed under the MIT License. See LICENSE for details.
//
// IR-driven Naming tests. Builds tiny Modules with parseAssemblyString +
// asserts Naming::get(Value&) round-trips. Complements the static-helper
// coverage in NamingTest.cpp (which doesn't touch a Module).
//
// Pattern reference for Phase 3.3 pass-level unit tests: subclass
// IRTestFixture, parseIR("..."), then exercise the API under test.
//

#include "IRTestFixture.h"

#include "smack/Naming.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"

using namespace smack;
using namespace smack::test;

class NamingIRTest : public IRTestFixture {};

TEST_F(NamingIRTest, NamedFunctionRoundTripsThroughGet) {
  parseIR(R"(
    define i32 @user_function(i32 %x) {
      ret i32 %x
    }
  )");

  llvm::Function *F = M->getFunction("user_function");
  ASSERT_NE(F, nullptr);

  Naming naming;
  std::string name = naming.get(*F);
  EXPECT_FALSE(name.empty());
  // Naming preserves user-visible names verbatim for named functions
  // (no $-prefix mangling).
  EXPECT_EQ(name, "user_function");
}

TEST_F(NamingIRTest, MultipleFunctionsHaveDistinctNames) {
  parseIR(R"(
    define void @alpha() { ret void }
    define void @beta()  { ret void }
  )");

  llvm::Function *a = M->getFunction("alpha");
  llvm::Function *b = M->getFunction("beta");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);

  Naming naming;
  EXPECT_NE(naming.get(*a), naming.get(*b));
}

TEST_F(NamingIRTest, FreshVarNameProducesDistinctNamesForSameValue) {
  parseIR(R"(
    define i32 @f() {
    entry:
      %tmp = add i32 1, 2
      ret i32 %tmp
    }
  )");

  llvm::Function *F = M->getFunction("f");
  ASSERT_NE(F, nullptr);
  llvm::Value *tmp = nullptr;
  for (auto &I : F->getEntryBlock()) {
    if (I.hasName() && I.getName() == "tmp")
      tmp = &I;
  }
  ASSERT_NE(tmp, nullptr);

  Naming naming;
  std::string a = naming.freshVarName(*tmp);
  std::string b = naming.freshVarName(*tmp);
  EXPECT_NE(a, b) << "freshVarName must mint distinct names on repeat calls";
}

TEST_F(NamingIRTest, FunctionFromSmackPrefixIsRecognized) {
  parseIR(R"(
    declare void @__SMACK_check_overflow(i32, i32, i32)
    declare void @user_func()
  )");

  EXPECT_TRUE(Naming::isSmackName("__SMACK_check_overflow"));
  EXPECT_FALSE(Naming::isSmackName("user_func"));

  llvm::Function *smackFn = M->getFunction("__SMACK_check_overflow");
  llvm::Function *userFn = M->getFunction("user_func");
  ASSERT_NE(smackFn, nullptr);
  ASSERT_NE(userFn, nullptr);
  EXPECT_TRUE(Naming::isSmackName(smackFn->getName()));
  EXPECT_FALSE(Naming::isSmackName(userFn->getName()));
}

TEST_F(NamingIRTest, ResetClearsPerInstanceCounters) {
  parseIR(R"(
    define i32 @g() {
    entry:
      %x = add i32 0, 0
      ret i32 %x
    }
  )");

  llvm::Function *F = M->getFunction("g");
  llvm::Value *x = &F->getEntryBlock().front();
  ASSERT_NE(x, nullptr);

  Naming naming;
  std::string before = naming.freshVarName(*x);
  naming.reset();
  std::string after = naming.freshVarName(*x);
  EXPECT_EQ(before, after);
}
