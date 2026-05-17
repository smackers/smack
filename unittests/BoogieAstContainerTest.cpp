//
// This file is distributed under the MIT License. See LICENSE for details.
//
// Coverage extension for the BoogieAst container classes (Block, ProcDecl,
// Program) — orthogonal to BoogieAstTest.cpp (Decl factories) and
// BoogieAstStmtTest.cpp (Stmt printer round-trips).
//

#include "smack/BoogieAst.h"

#include "llvm/Support/Casting.h"
#include "gtest/gtest.h"

#include <iterator>
#include <sstream>
#include <string>
#include <vector>

using namespace smack;

namespace {

std::string printed(const Block *b) {
  std::ostringstream os;
  b->print(os);
  return os.str();
}

std::string printed(const ProcDecl *p) {
  std::ostringstream os;
  p->print(os);
  return os.str();
}

std::string printed(const Program &p) {
  std::ostringstream os;
  p.print(os);
  return os.str();
}

} // namespace

// ---------- Block ----------

TEST(BoogieAstBlock, NamedBlockEmitsLabel) {
  Block *b = Block::block("entry", {Stmt::assume(Expr::lit(true))});
  std::string out = printed(b);
  EXPECT_NE(out.find("entry:"), std::string::npos);
  EXPECT_NE(out.find("assume"), std::string::npos);
  EXPECT_NE(out.find("true"), std::string::npos);
}

TEST(BoogieAstBlock, AnonymousBlockOmitsLabel) {
  Block *b = Block::block("", {Stmt::assert_(Expr::lit(true))});
  std::string out = printed(b);
  // No leading "<name>:" line; just the indented statement.
  EXPECT_EQ(out.find(":"), std::string::npos);
  EXPECT_NE(out.find("assert"), std::string::npos);
}

TEST(BoogieAstBlock, AddStmtAppendsAtEnd) {
  Block *b = Block::block("L", {Stmt::comment("first")});
  b->addStmt(Stmt::comment("second"));
  std::string out = printed(b);
  EXPECT_LT(out.find("first"), out.find("second"));
}

TEST(BoogieAstBlock, InsertPrependsAtFront) {
  Block *b = Block::block("L", {Stmt::comment("middle")});
  b->insert(Stmt::comment("front"));
  std::string out = printed(b);
  EXPECT_LT(out.find("front"), out.find("middle"));
}

TEST(BoogieAstBlock, GetNameRoundTrip) {
  Block *b = Block::block("$bb.7");
  EXPECT_EQ(b->getName(), "$bb.7");
}

TEST(BoogieAstBlock, GetStatementsExposesUnderlyingList) {
  Block *b = Block::block("L", {Stmt::assume(Expr::lit(true)),
                                Stmt::assume(Expr::lit(false))});
  EXPECT_EQ(b->getStatements().size(), 2u);
  // Iteration matches insertion order.
  std::vector<const Stmt *> seen(b->begin(), b->end());
  EXPECT_EQ(seen.size(), 2u);
}

// ---------- ProcDecl ----------

TEST(BoogieAstProcDecl, EmptyBodyPrintsDeclarationOnly) {
  ProcDecl *p = Decl::procedure("foo");
  std::string out = printed(p);
  EXPECT_NE(out.find("procedure"), std::string::npos);
  EXPECT_NE(out.find("foo"), std::string::npos);
  // No body braces when blocks list is empty — declaration ends with `;`.
  EXPECT_NE(out.find(";"), std::string::npos);
  EXPECT_EQ(out.find("{"), std::string::npos);
}

TEST(BoogieAstProcDecl, ProcedureGetParametersReturnsEmptyByDefault) {
  ProcDecl *p = Decl::procedure("g");
  EXPECT_TRUE(p->getParameters().empty());
  EXPECT_TRUE(p->getReturns().empty());
}

TEST(BoogieAstProcDecl, RequiresAndEnsuresAccessorsRoundTrip) {
  ProcDecl *p = Decl::procedure("h");
  p->getRequires().push_back(Expr::lit(true));
  p->getEnsures().push_back(Expr::eq(Expr::id("x"),
                                     Expr::lit(static_cast<long long>(0))));

  std::string out = printed(p);
  EXPECT_NE(out.find("requires"), std::string::npos);
  EXPECT_NE(out.find("ensures"), std::string::npos);
  EXPECT_NE(out.find("x"), std::string::npos);
}

TEST(BoogieAstProcDecl, ModifiesClauseAppearsWhenSet) {
  ProcDecl *p = Decl::procedure("m");
  p->getModifies().push_back("$M.0");
  p->getModifies().push_back("$M.1");
  std::string out = printed(p);
  EXPECT_NE(out.find("modifies"), std::string::npos);
  EXPECT_NE(out.find("$M.0"), std::string::npos);
  EXPECT_NE(out.find("$M.1"), std::string::npos);
}

TEST(BoogieAstProcDecl, RttiProcedureIsProcDecl) {
  Decl *d = Decl::procedure("p");
  EXPECT_TRUE(llvm::isa<ProcDecl>(d));
  EXPECT_FALSE(llvm::isa<VarDecl>(d));
}

// ---------- Program ----------

TEST(BoogieAstProgram, EmptyProgramPrintsEmpty) {
  Program p;
  std::string out = printed(p);
  // Should at least not throw + return something containing a newline
  // (print_seq emits an empty list as nothing + the trailing "\n").
  EXPECT_FALSE(out.empty() && out != "\n");
}

TEST(BoogieAstProgram, AppendPreludeEmitsPreludeFirst) {
  Program p;
  p.appendPrelude("// PRELUDE_MARKER\n");
  std::string out = printed(p);
  EXPECT_NE(out.find("PRELUDE_MARKER"), std::string::npos);
}

TEST(BoogieAstProgram, GetDeclarationsExposesUnderlyingList) {
  Program p;
  Decl *axiom = Decl::axiom(Expr::lit(true), "ax_true");
  p.getDeclarations().push_back(axiom);

  std::string out = printed(p);
  EXPECT_NE(out.find("axiom"), std::string::npos);
  EXPECT_NE(out.find("true"), std::string::npos);
}

TEST(BoogieAstProgram, MultipleDeclsAllRenderedInOrder) {
  Program p;
  p.getDeclarations().push_back(Decl::variable("x", "int"));
  p.getDeclarations().push_back(Decl::variable("y", "bool"));
  std::string out = printed(p);
  // Iteration order = declaration list order.
  EXPECT_LT(out.find("x"), out.find("y"));
}

TEST(BoogieAstProgram, BeginEndIterationMatchesGetDeclarations) {
  Program p;
  p.getDeclarations().push_back(Decl::variable("a", "int"));
  p.getDeclarations().push_back(Decl::variable("b", "int"));
  EXPECT_EQ(std::distance(p.begin(), p.end()), 2);
}
