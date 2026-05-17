//
// This file is distributed under the MIT License. See LICENSE for details.
//
// Smoke tests for smack::Naming static helpers.
//

#include "smack/Naming.h"
#include "gtest/gtest.h"

#include <string>

using namespace smack;

TEST(NamingSmackName, MatchesSmackPrefix) {
  EXPECT_TRUE(Naming::isSmackName("__SMACK_check_overflow"));
  EXPECT_TRUE(Naming::isSmackName("foo__SMACK_bar"));
}

TEST(NamingSmackName, RejectsUserNames) {
  EXPECT_FALSE(Naming::isSmackName("main"));
  EXPECT_FALSE(Naming::isSmackName(""));
  EXPECT_FALSE(Naming::isSmackName("user_function"));
  EXPECT_FALSE(Naming::isSmackName("__VERIFIER_assume"));
}

TEST(NamingGenerated, DollarPrefixedIsGenerated) {
  EXPECT_TRUE(Naming::isSmackGeneratedName("$tmp"));
  EXPECT_TRUE(Naming::isSmackGeneratedName("$1"));
}

TEST(NamingGenerated, NonDollarIsNotGenerated) {
  EXPECT_FALSE(Naming::isSmackGeneratedName("tmp"));
  EXPECT_FALSE(Naming::isSmackGeneratedName(""));
  EXPECT_FALSE(Naming::isSmackGeneratedName("foo$bar"));
}

TEST(NamingBplKeyword, ReservedKeywordsMatch) {
  EXPECT_TRUE(Naming::isBplKeyword("var"));
  EXPECT_TRUE(Naming::isBplKeyword("axiom"));
  EXPECT_TRUE(Naming::isBplKeyword("procedure"));
  EXPECT_TRUE(Naming::isBplKeyword("forall"));
  EXPECT_TRUE(Naming::isBplKeyword("ensures"));
}

TEST(NamingBplKeyword, IdentifiersDoNotMatch) {
  EXPECT_FALSE(Naming::isBplKeyword("variable"));
  EXPECT_FALSE(Naming::isBplKeyword("Var"));
  EXPECT_FALSE(Naming::isBplKeyword(""));
  EXPECT_FALSE(Naming::isBplKeyword("user_var"));
}

TEST(NamingEscape, ReplacesAtSignWithDot) {
  EXPECT_EQ(Naming::escape("foo@bar"), "foo.bar");
}

TEST(NamingEscape, EmptyStringRoundTrips) {
  EXPECT_EQ(Naming::escape(""), "");
}

TEST(NamingEscape, PlainIdentifierUnchanged) {
  EXPECT_EQ(Naming::escape("plain_name"), "plain_name");
}

TEST(NamingFresh, BlockNamesAreUniquePerInstance) {
  Naming n;
  std::string a = n.freshBlockName();
  std::string b = n.freshBlockName();
  EXPECT_NE(a, b);
}

TEST(NamingFresh, GlobalNamesAreUniquePerInstance) {
  Naming n;
  std::string a = n.freshGlobalName();
  std::string b = n.freshGlobalName();
  EXPECT_NE(a, b);
}

TEST(NamingFresh, ResetRestartsCounters) {
  Naming n;
  std::string before = n.freshBlockName();
  n.reset();
  std::string after = n.freshBlockName();
  EXPECT_EQ(before, after);
}

TEST(NamingIntWrap, SignedAndUnsignedDiffer) {
  std::string s = Naming::getIntWrapFunc(false);
  std::string u = Naming::getIntWrapFunc(true);
  EXPECT_FALSE(s.empty());
  EXPECT_FALSE(u.empty());
  EXPECT_NE(s, u);
}
