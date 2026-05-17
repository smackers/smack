//
// This file is distributed under the MIT License. See LICENSE for details.
//
// Smoke tests for smack::Expr / smack::Decl factories and printers.
// Foundation for Phase A5 (NewPM migration) regression checks: any change to
// the IR-to-Boogie translation should preserve these AST round-trips.
//

#include "smack/BoogieAst.h"
#include "gtest/gtest.h"

#include <sstream>
#include <string>

using namespace smack;

namespace {

std::string printed(const Decl *d) {
  std::ostringstream os;
  d->print(os);
  return os.str();
}

std::string printed(const Expr *e) {
  std::ostringstream os;
  e->print(os);
  return os.str();
}

} // namespace

TEST(BoogieAstDecl, AxiomCarriesNameAndExpr) {
  const Expr *e = Expr::lit(true);
  Decl *d = Decl::axiom(e, "trivially_true");
  EXPECT_EQ(d->getName(), "trivially_true");
  std::string s = printed(d);
  EXPECT_NE(s.find("axiom"), std::string::npos);
  EXPECT_NE(s.find("true"), std::string::npos);
}

TEST(BoogieAstDecl, ConstantPrintsNameAndType) {
  Decl *d = Decl::constant("counter", "int");
  EXPECT_EQ(d->getName(), "counter");
  std::string s = printed(d);
  EXPECT_NE(s.find("const"), std::string::npos);
  EXPECT_NE(s.find("counter"), std::string::npos);
  EXPECT_NE(s.find("int"), std::string::npos);
}

TEST(BoogieAstDecl, VariablePrintsNameAndType) {
  Decl *d = Decl::variable("x", "bool");
  EXPECT_EQ(d->getName(), "x");
  std::string s = printed(d);
  EXPECT_NE(s.find("x"), std::string::npos);
  EXPECT_NE(s.find("bool"), std::string::npos);
}

TEST(BoogieAstDecl, IdsAreUnique) {
  Decl *a = Decl::variable("a", "int");
  Decl *b = Decl::variable("b", "int");
  EXPECT_NE(a->getId(), b->getId());
}

TEST(BoogieAstExpr, BoolLitPrints) {
  EXPECT_EQ(printed(Expr::lit(true)), "true");
  EXPECT_EQ(printed(Expr::lit(false)), "false");
}

TEST(BoogieAstExpr, IntLitPrintsValue) {
  std::string s = printed(Expr::lit(static_cast<long long>(42)));
  EXPECT_NE(s.find("42"), std::string::npos);
}

TEST(BoogieAstExpr, IdentifierPrintsName) {
  EXPECT_EQ(printed(Expr::id("counter")), "counter");
}

TEST(BoogieAstExpr, EqualityCombinesOperands) {
  const Expr *e =
      Expr::eq(Expr::id("a"), Expr::lit(static_cast<long long>(42)));
  std::string s = printed(e);
  EXPECT_NE(s.find("a"), std::string::npos);
  EXPECT_NE(s.find("42"), std::string::npos);
  EXPECT_NE(s.find("=="), std::string::npos);
}

TEST(BoogieAstExpr, AndCombinesOperands) {
  const Expr *e = Expr::and_(Expr::lit(true), Expr::id("p"));
  std::string s = printed(e);
  EXPECT_NE(s.find("true"), std::string::npos);
  EXPECT_NE(s.find("p"), std::string::npos);
  EXPECT_NE(s.find("&&"), std::string::npos);
}
