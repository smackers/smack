//
// This file is distributed under the MIT License. See LICENSE for details.
//
// Coverage extension for the BoogieAst Stmt + Expr factories not exercised
// by BoogieAstTest.cpp. Same printer round-trip pattern: build the AST,
// print to an ostream, assert that key substrings appear. Any change that
// reorders the Boogie source SMACK emits would break these tests, so they
// pin the textual contract that downstream tools (Boogie, Corral, the
// parser) rely on.
//

#include "smack/BoogieAst.h"

#include "llvm/Support/Casting.h"
#include "gtest/gtest.h"

#include <sstream>
#include <string>

using namespace smack;

namespace {

std::string printed(const Stmt *s) {
  std::ostringstream os;
  s->print(os);
  return os.str();
}

std::string printed(const Expr *e) {
  std::ostringstream os;
  e->print(os);
  return os.str();
}

} // namespace

// ---------- Stmt factories ----------

TEST(BoogieAstStmt, AssertCarriesCondition) {
  const Stmt *s = Stmt::assert_(Expr::lit(true));
  std::string out = printed(s);
  EXPECT_NE(out.find("assert"), std::string::npos);
  EXPECT_NE(out.find("true"), std::string::npos);
}

TEST(BoogieAstStmt, AssumeCarriesCondition) {
  const Stmt *s = Stmt::assume(Expr::eq(Expr::id("x"),
                                        Expr::lit(static_cast<long long>(0))));
  std::string out = printed(s);
  EXPECT_NE(out.find("assume"), std::string::npos);
  EXPECT_NE(out.find("x"), std::string::npos);
  EXPECT_NE(out.find("0"), std::string::npos);
}

TEST(BoogieAstStmt, AssignSingleLhsRhs) {
  const Stmt *s = Stmt::assign(Expr::id("x"),
                               Expr::lit(static_cast<long long>(7)));
  std::string out = printed(s);
  EXPECT_NE(out.find("x"), std::string::npos);
  EXPECT_NE(out.find(":="), std::string::npos);
  EXPECT_NE(out.find("7"), std::string::npos);
}

TEST(BoogieAstStmt, HavocVariableMentionsName) {
  const Stmt *s = Stmt::havoc("nondet_in");
  std::string out = printed(s);
  EXPECT_NE(out.find("havoc"), std::string::npos);
  EXPECT_NE(out.find("nondet_in"), std::string::npos);
}

TEST(BoogieAstStmt, GotoMentionsAllTargets) {
  const Stmt *s = Stmt::goto_({"L1", "L2", "L3"});
  std::string out = printed(s);
  EXPECT_NE(out.find("goto"), std::string::npos);
  EXPECT_NE(out.find("L1"), std::string::npos);
  EXPECT_NE(out.find("L2"), std::string::npos);
  EXPECT_NE(out.find("L3"), std::string::npos);
}

TEST(BoogieAstStmt, CommentEmitsTextWithBlockCommentSyntax) {
  const Stmt *s = Stmt::comment("hello-world");
  std::string out = printed(s);
  EXPECT_NE(out.find("hello-world"), std::string::npos);
  // SMACK emits comments as `/* ... */` so they survive Boogie's
  // single-line-comment-eats-rest-of-line behaviour.
  EXPECT_NE(out.find("/*"), std::string::npos);
  EXPECT_NE(out.find("*/"), std::string::npos);
}

TEST(BoogieAstStmt, ReturnVoidMentionsReturnKeyword) {
  const Stmt *s = Stmt::return_();
  std::string out = printed(s);
  EXPECT_NE(out.find("return"), std::string::npos);
}

TEST(BoogieAstStmt, IfStmtEmitsThenAndElseBranches) {
  const Stmt *thn = Stmt::assert_(Expr::lit(true));
  const Stmt *els = Stmt::assert_(Expr::lit(false));
  const Stmt *s = Stmt::if_(Expr::id("c"), {thn}, {els});
  std::string out = printed(s);
  EXPECT_NE(out.find("if"), std::string::npos);
  EXPECT_NE(out.find("else"), std::string::npos);
  EXPECT_NE(out.find("c"), std::string::npos);
  EXPECT_NE(out.find("true"), std::string::npos);
  EXPECT_NE(out.find("false"), std::string::npos);
}

TEST(BoogieAstStmt, WhileStmtEmitsGuardAndInvariants) {
  const Expr *inv =
      Expr::lt(Expr::id("i"), Expr::lit(static_cast<long long>(10)));
  const Stmt *body =
      Stmt::assign(Expr::id("i"),
                   Expr::id("i") /* trivial body — printer test only */);
  const Stmt *s = Stmt::while_(Expr::lt(Expr::id("i"),
                                        Expr::lit(static_cast<long long>(10))),
                               {inv}, {body});
  std::string out = printed(s);
  EXPECT_NE(out.find("while"), std::string::npos);
  EXPECT_NE(out.find("invariant"), std::string::npos);
  EXPECT_NE(out.find("i"), std::string::npos);
  EXPECT_NE(out.find("10"), std::string::npos);
}

TEST(BoogieAstStmt, BreakIsEmitted) {
  const Stmt *s = Stmt::break_();
  EXPECT_NE(printed(s).find("break"), std::string::npos);
}

TEST(BoogieAstStmt, CallEmitsProcedureNameAndArgs) {
  const Stmt *s = Stmt::call("__SMACK_check_overflow",
                             {Expr::id("a"), Expr::id("b")},
                             {"result"});
  std::string out = printed(s);
  EXPECT_NE(out.find("call"), std::string::npos);
  EXPECT_NE(out.find("__SMACK_check_overflow"), std::string::npos);
  EXPECT_NE(out.find("a"), std::string::npos);
  EXPECT_NE(out.find("b"), std::string::npos);
  EXPECT_NE(out.find("result"), std::string::npos);
}

// ---------- Stmt RTTI (llvm::isa via classof) ----------

TEST(BoogieAstStmt, RttiAssertIsAssertStmt) {
  const Stmt *s = Stmt::assert_(Expr::lit(true));
  EXPECT_TRUE(llvm::isa<AssertStmt>(s));
  EXPECT_FALSE(llvm::isa<AssumeStmt>(s));
}

TEST(BoogieAstStmt, RttiAssumeIsAssumeStmt) {
  const Stmt *s = Stmt::assume(Expr::lit(true));
  EXPECT_TRUE(llvm::isa<AssumeStmt>(s));
  EXPECT_FALSE(llvm::isa<AssertStmt>(s));
}

TEST(BoogieAstStmt, RttiHavocIsHavocStmt) {
  const Stmt *s = Stmt::havoc("x");
  EXPECT_TRUE(llvm::isa<HavocStmt>(s));
}

TEST(BoogieAstStmt, RttiGotoIsGotoStmt) {
  const Stmt *s = Stmt::goto_({"L1"});
  EXPECT_TRUE(llvm::isa<GotoStmt>(s));
}

TEST(BoogieAstStmt, RttiReturnIsReturnStmt) {
  const Stmt *s = Stmt::return_();
  EXPECT_TRUE(llvm::isa<ReturnStmt>(s));
}

TEST(BoogieAstStmt, RttiIfIsIfStmt) {
  const Stmt *s = Stmt::if_(Expr::lit(true), {}, {});
  EXPECT_TRUE(llvm::isa<IfStmt>(s));
}

TEST(BoogieAstStmt, RttiWhileIsWhileStmt) {
  const Stmt *s = Stmt::while_(Expr::lit(true), {}, {});
  EXPECT_TRUE(llvm::isa<WhileStmt>(s));
}

TEST(BoogieAstStmt, RttiCallIsCallStmt) {
  const Stmt *s = Stmt::call("foo");
  EXPECT_TRUE(llvm::isa<CallStmt>(s));
}

TEST(BoogieAstStmt, RttiCommentIsComment) {
  const Stmt *s = Stmt::comment("note");
  EXPECT_TRUE(llvm::isa<Comment>(s));
}

// ---------- AssumeStmt-specific accessors ----------

TEST(BoogieAstStmt, AssumeHasAttrTracksAddedAttribute) {
  AssumeStmt *s = const_cast<AssumeStmt *>(
      llvm::cast<AssumeStmt>(Stmt::assume(Expr::lit(true))));
  EXPECT_FALSE(s->hasAttr("partition"));
  s->add(Attr::attr("partition"));
  EXPECT_TRUE(s->hasAttr("partition"));
  EXPECT_FALSE(s->hasAttr("other-attr"));
}

TEST(BoogieAstStmt, AssumeGetExprRoundTrips) {
  const Expr *e = Expr::eq(Expr::id("x"),
                           Expr::lit(static_cast<long long>(0)));
  const Stmt *s = Stmt::assume(e);
  auto *as = llvm::cast<AssumeStmt>(s);
  EXPECT_EQ(as->getExpr(), e);
}

// ---------- GotoStmt accessor ----------

TEST(BoogieAstStmt, GotoGetTargetsReturnsAll) {
  const Stmt *s = Stmt::goto_({"L1", "L2", "L3"});
  auto *g = llvm::cast<GotoStmt>(s);
  ASSERT_EQ(g->getTargets().size(), 3u);
  auto it = g->getTargets().begin();
  EXPECT_EQ(*it++, "L1");
  EXPECT_EQ(*it++, "L2");
  EXPECT_EQ(*it, "L3");
}

// ---------- Additional Expr factories ----------

TEST(BoogieAstExpr, NotPrintsExclamation) {
  const Expr *e = Expr::not_(Expr::id("p"));
  std::string out = printed(e);
  EXPECT_NE(out.find("!"), std::string::npos);
  EXPECT_NE(out.find("p"), std::string::npos);
}

TEST(BoogieAstExpr, NeqUsesBangEquals) {
  const Expr *e = Expr::neq(Expr::id("a"), Expr::id("b"));
  std::string out = printed(e);
  EXPECT_NE(out.find("!="), std::string::npos);
}

TEST(BoogieAstExpr, ImplUsesArrow) {
  const Expr *e = Expr::impl(Expr::id("p"), Expr::id("q"));
  std::string out = printed(e);
  // Boogie's implication operator renders as `==>`.
  EXPECT_NE(out.find("==>"), std::string::npos);
  EXPECT_NE(out.find("p"), std::string::npos);
  EXPECT_NE(out.find("q"), std::string::npos);
}

TEST(BoogieAstExpr, OrUsesDoublePipe) {
  const Expr *e = Expr::or_(Expr::id("p"), Expr::id("q"));
  std::string out = printed(e);
  EXPECT_NE(out.find("||"), std::string::npos);
}

TEST(BoogieAstExpr, LtUsesLessThan) {
  const Expr *e =
      Expr::lt(Expr::id("i"), Expr::lit(static_cast<long long>(10)));
  std::string out = printed(e);
  EXPECT_NE(out.find("<"), std::string::npos);
  EXPECT_NE(out.find("i"), std::string::npos);
  EXPECT_NE(out.find("10"), std::string::npos);
}

TEST(BoogieAstExpr, SelectByExprPrintsSquareBrackets) {
  const Expr *e =
      Expr::sel(Expr::id("M"), Expr::id("p"));
  std::string out = printed(e);
  // Boogie map-select syntax is `M[p]`.
  EXPECT_NE(out.find("M"), std::string::npos);
  EXPECT_NE(out.find("p"), std::string::npos);
  EXPECT_NE(out.find("["), std::string::npos);
  EXPECT_NE(out.find("]"), std::string::npos);
}

TEST(BoogieAstExpr, SelectByStringFormShorthand) {
  // sel(string, string) is the shorthand SmackRep uses when both map
  // and index are plain identifiers.
  const Expr *e = Expr::sel("M", "p");
  std::string out = printed(e);
  EXPECT_NE(out.find("M"), std::string::npos);
  EXPECT_NE(out.find("p"), std::string::npos);
}

TEST(BoogieAstExpr, UpdateRendersThreeOperands) {
  const Expr *e = Expr::upd(Expr::id("M"), Expr::id("p"),
                            Expr::lit(static_cast<long long>(0)));
  std::string out = printed(e);
  // Boogie map-update is `M[p := 0]`.
  EXPECT_NE(out.find("M"), std::string::npos);
  EXPECT_NE(out.find("p"), std::string::npos);
  EXPECT_NE(out.find(":="), std::string::npos);
  EXPECT_NE(out.find("0"), std::string::npos);
}

TEST(BoogieAstExpr, FunctionApplicationEmitsArgsInParens) {
  const Expr *e =
      Expr::fn("$bvadd", Expr::id("a"), Expr::id("b"));
  std::string out = printed(e);
  EXPECT_NE(out.find("$bvadd"), std::string::npos);
  EXPECT_NE(out.find("a"), std::string::npos);
  EXPECT_NE(out.find("b"), std::string::npos);
  EXPECT_NE(out.find("("), std::string::npos);
  EXPECT_NE(out.find(")"), std::string::npos);
}

TEST(BoogieAstExpr, BitvectorLitCarriesWidthSuffix) {
  // lit(value, width) — Boogie bitvector literal renders as `42bv8`.
  const Expr *e =
      Expr::lit(static_cast<unsigned long long>(42), 8u);
  std::string out = printed(e);
  EXPECT_NE(out.find("42"), std::string::npos);
  EXPECT_NE(out.find("bv8"), std::string::npos);
}

TEST(BoogieAstExpr, BvConcatEmitsConcatOperator) {
  const Expr *e = Expr::bvConcat(Expr::id("hi"), Expr::id("lo"));
  std::string out = printed(e);
  // Boogie bitvector concat is `++`.
  EXPECT_NE(out.find("++"), std::string::npos);
  EXPECT_NE(out.find("hi"), std::string::npos);
  EXPECT_NE(out.find("lo"), std::string::npos);
}
