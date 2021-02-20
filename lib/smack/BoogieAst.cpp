//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/BoogieAst.h"
#include "smack/Naming.h"
#include "llvm/IR/Constants.h"
#include <iostream>
#include <set>
#include <sstream>

namespace smack {

unsigned Decl::uniqueId = 0;

const Expr *Expr::exists(std::list<Binding> vars, const Expr *e) {
  return new QuantExpr(QuantExpr::Exists, vars, e);
}

const Expr *Expr::forall(std::list<Binding> vars, const Expr *e) {
  return new QuantExpr(QuantExpr::Forall, vars, e);
}

const Expr *Expr::and_(const Expr *l, const Expr *r) {
  return new BinExpr(BinExpr::And, l, r);
}

const Expr *Expr::or_(const Expr *l, const Expr *r) {
  return new BinExpr(BinExpr::Or, l, r);
}

const Expr *Expr::eq(const Expr *l, const Expr *r) {
  return new BinExpr(BinExpr::Eq, l, r);
}

const Expr *Expr::lt(const Expr *l, const Expr *r) {
  return new BinExpr(BinExpr::Lt, l, r);
}

const Expr *Expr::ifThenElse(const Expr *c, const Expr *t, const Expr *e) {
  return new IfThenElseExpr(c, t, e);
}

const Expr *Expr::fn(std::string f, std::list<const Expr *> args) {
  return new FunExpr(f, args);
}

const Expr *Expr::fn(std::string f, const Expr *x) {
  return new FunExpr(f, std::list<const Expr *>(1, x));
}

const Expr *Expr::fn(std::string f, const Expr *x, const Expr *y) {
  std::list<const Expr *> ps;
  ps.push_back(x);
  ps.push_back(y);
  return new FunExpr(f, ps);
}

const Expr *Expr::fn(std::string f, const Expr *x, const Expr *y,
                     const Expr *z) {
  std::list<const Expr *> ps;
  ps.push_back(x);
  ps.push_back(y);
  ps.push_back(z);
  return new FunExpr(f, ps);
}

const Expr *Expr::id(std::string s) { return new VarExpr(s); }

const Expr *Expr::impl(const Expr *l, const Expr *r) {
  return new BinExpr(BinExpr::Imp, l, r);
}

const Expr *Expr::lit(bool b) { return new BoolLit(b); }

const Expr *Expr::lit(std::string v) { return new StringLit(v); }

const Expr *Expr::lit(unsigned long long v) { return new IntLit(v); }

const Expr *Expr::lit(long long v) { return new IntLit(v); }

const Expr *Expr::lit(std::string v, unsigned w) {
  return w ? (const Expr *)new BvLit(v, w) : (const Expr *)new IntLit(v);
}

const Expr *Expr::lit(unsigned long long v, unsigned w) {
  return new BvLit(v, w);
}

const Expr *Expr::lit(bool n, std::string s, std::string e, unsigned ss,
                      unsigned es) {
  return new FPLit(n, s, e, ss, es);
}

const Expr *Expr::lit(std::string v, unsigned ss, unsigned es) {
  return new FPLit(v, ss, es);
}

const Expr *Expr::lit(RModeKind v) { return new RModeLit(v); }

const Expr *Expr::neq(const Expr *l, const Expr *r) {
  return new BinExpr(BinExpr::Neq, l, r);
}

const Expr *Expr::not_(const Expr *e) { return new NotExpr(e); }

const Expr *Expr::sel(const Expr *b, const Expr *i) {
  return new SelExpr(b, i);
}

const Expr *Expr::sel(std::string b, std::string i) {
  return new SelExpr(id(b), id(i));
}

const Expr *Expr::upd(const Expr *b, const Expr *i, const Expr *v) {
  return new UpdExpr(b, i, v);
}

const Expr *Expr::bvExtract(const Expr *v, const Expr *u, const Expr *l) {
  return new BvExtract(v, u, l);
}

const Expr *Expr::bvExtract(const Expr *v, unsigned u, unsigned l) {
  return new BvExtract(v, Expr::lit(u), Expr::lit(l));
}

const Expr *Expr::bvExtract(std::string v, unsigned u, unsigned l) {
  return new BvExtract(Expr::id(v), Expr::lit(u), Expr::lit(l));
}

const Expr *Expr::bvConcat(const Expr *left, const Expr *right) {
  return new BvConcat(left, right);
}

const Attr *Attr::attr(std::string s, std::initializer_list<const Expr *> vs) {
  return new Attr(s, vs);
}

const Attr *Attr::attr(std::string s, std::list<const Expr *> vs) {
  return new Attr(s, vs);
}

const Attr *Attr::attr(std::string s) { return attr(s, {}); }

const Attr *Attr::attr(std::string s, std::string v) {
  return new Attr(s, {Expr::lit(v)});
}

const Attr *Attr::attr(std::string s, int v) {
  return attr(s, {Expr::lit((long long)v)});
}

const Attr *Attr::attr(std::string s, std::string v, int i) {
  return attr(s, {Expr::lit(v), Expr::lit((long long)i)});
}

const Attr *Attr::attr(std::string s, std::string v, int i, int j) {
  return attr(s,
              {Expr::lit(v), Expr::lit((long long)i), Expr::lit((long long)j)});
}

const Stmt *Stmt::annot(std::list<const Attr *> attrs) {
  AssumeStmt *s = new AssumeStmt(Expr::lit(true));
  for (auto A : attrs)
    s->add(A);
  return s;
}

const Stmt *Stmt::annot(const Attr *a) {
  return Stmt::annot(std::list<const Attr *>(1, a));
}

const Stmt *Stmt::assert_(const Expr *e, std::list<const Attr *> attrs) {
  return new AssertStmt(e, attrs);
}

const Stmt *Stmt::assign(const Expr *e, const Expr *f) {
  return new AssignStmt(std::list<const Expr *>(1, e),
                        std::list<const Expr *>(1, f));
}

const Stmt *Stmt::assign(std::list<const Expr *> lhs,
                         std::list<const Expr *> rhs) {
  return new AssignStmt(lhs, rhs);
}

const Stmt *Stmt::assume(const Expr *e) { return new AssumeStmt(e); }

const Stmt *Stmt::assume(const Expr *e, const Attr *a) {
  AssumeStmt *s = new AssumeStmt(e);
  s->add(a);
  return (const AssumeStmt *)s;
}

const Stmt *Stmt::call(std::string p, std::list<const Expr *> args,
                       std::list<std::string> rets,
                       std::list<const Attr *> attrs) {
  return new CallStmt(p, attrs, args, rets);
}

const Stmt *Stmt::comment(std::string s) { return new Comment(s); }

const Stmt *Stmt::goto_(std::list<std::string> ts) { return new GotoStmt(ts); }

const Stmt *Stmt::havoc(std::string x) {
  return new HavocStmt(std::list<std::string>(1, x));
}

const Stmt *Stmt::havoc(const Expr *x) {
  std::stringstream s;
  s << x;
  return new HavocStmt(std::list<std::string>(1, s.str()));
}

const Stmt *Stmt::return_(const Expr *e) { return new ReturnStmt(e); }

const Stmt *Stmt::return_() { return new ReturnStmt(); }

const Stmt *Stmt::skip() { return new AssumeStmt(Expr::lit(true)); }

const Stmt *Stmt::code(std::string s) { return new CodeStmt(s); }

Decl *Decl::typee(std::string name, std::string type,
                  std::list<const Attr *> attrs) {
  return new TypeDecl(name, type, attrs);
}
Decl *Decl::axiom(const Expr *e, std::string name) {
  return new AxiomDecl(name, e);
}
FuncDecl *Decl::function(std::string name, std::list<Binding> args,
                         std::string type, const Expr *e,
                         std::list<const Attr *> attrs) {
  return new FuncDecl(name, attrs, args, type, e);
}
Decl *Decl::constant(std::string name, std::string type) {
  return Decl::constant(name, type, std::list<const Attr *>(), false);
}
Decl *Decl::constant(std::string name, std::string type, bool unique) {
  return Decl::constant(name, type, std::list<const Attr *>(), unique);
}
Decl *Decl::constant(std::string name, std::string type,
                     std::list<const Attr *> ax, bool unique) {
  return new ConstDecl(name, type, ax, unique);
}
Decl *Decl::variable(std::string name, std::string type) {
  return new VarDecl(name, type);
}
ProcDecl *Decl::procedure(std::string name, std::list<Binding> args,
                          std::list<Binding> rets, std::list<Decl *> decls,
                          std::list<Block *> blocks) {
  return new ProcDecl(name, args, rets, decls, blocks);
}
Decl *Decl::code(std::string name, std::string s) {
  return new CodeDecl(name, s);
}

FuncDecl *Decl::code(ProcDecl *P) {
  std::list<Decl *> decls;
  std::list<Block *> blocks;
  for (auto B : *P) {
    blocks.push_back(Block::block(B->getName()));
    for (auto S : *B) {
      const Stmt *SS;
      if (llvm::isa<ReturnStmt>(S))
        SS = Stmt::return_(
            Expr::neq(Expr::id(P->getReturns().front().first), Expr::lit(0U)));
      else
        SS = S;
      blocks.back()->getStatements().push_back(SS);
    }
  }
  for (auto D : P->getDeclarations())
    decls.push_back(D);

  // HACK to avoid spurious global-var modification
  decls.push_back(Decl::variable(Naming::EXN_VAR, "bool"));

  for (auto R : P->getReturns())
    decls.push_back(Decl::variable(R.first, R.second));

  return Decl::function(P->getName(), P->getParameters(), "bool",
                        new CodeExpr(decls, blocks), {Attr::attr("inline")});
}

std::ostream &operator<<(std::ostream &os, const Expr &e) {
  e.print(os);
  return os;
}
std::ostream &operator<<(std::ostream &os, const Expr *e) {
  e->print(os);
  return os;
}
std::ostream &operator<<(std::ostream &os, const Attr *a) {
  a->print(os);
  return os;
}
std::ostream &operator<<(std::ostream &os, const Stmt *s) {
  s->print(os);
  return os;
}
std::ostream &operator<<(std::ostream &os, const Block *b) {
  b->print(os);
  return os;
}
std::ostream &operator<<(std::ostream &os, Decl &d) {
  d.print(os);
  return os;
}
std::ostream &operator<<(std::ostream &os, Decl *d) {
  d->print(os);
  return os;
}
std::ostream &operator<<(std::ostream &os, Program *p) {
  if (p == 0) {
    os << "<null> Program!\n";
  } else {
    p->print(os);
  }
  return os;
}
std::ostream &operator<<(std::ostream &os, Program &p) {
  p.print(os);
  return os;
}

template <class T, class U>
std::ostream &operator<<(std::ostream &os, std::pair<T, U> p) {
  os << p.first << ": " << p.second;
  return os;
}

template <class T>
void print_seq(std::ostream &os, std::list<T> ts, std::string init,
               std::string sep, std::string term) {

  os << init;
  for (typename std::list<T>::iterator i = ts.begin(); i != ts.end(); ++i)
    os << (i == ts.begin() ? "" : sep) << *i;
  os << term;
}
template <class T>
void print_seq(std::ostream &os, std::list<T> ts, std::string sep) {
  print_seq<T>(os, ts, "", sep, "");
}
template <class T> void print_seq(std::ostream &os, std::list<T> ts) {
  print_seq<T>(os, ts, "", "", "");
}
template <class T, class C>
void print_set(std::ostream &os, std::set<T, C> ts, std::string init,
               std::string sep, std::string term) {

  os << init;
  for (typename std::set<T, C>::iterator i = ts.begin(); i != ts.end(); ++i)
    os << (i == ts.begin() ? "" : sep) << *i;
  os << term;
}
template <class T, class C>
void print_set(std::ostream &os, std::set<T, C> ts, std::string sep) {
  print_set<T, C>(os, ts, "", sep, "");
}
template <class T, class C>
void print_set(std::ostream &os, std::set<T, C> ts) {
  print_set<T, C>(os, ts, "", "", "");
}

void BinExpr::print(std::ostream &os) const {
  os << "(" << lhs << " ";
  switch (op) {
  case Iff:
    os << "<==>";
    break;
  case Imp:
    os << "==>";
    break;
  case Or:
    os << "||";
    break;
  case And:
    os << "&&";
    break;
  case Eq:
    os << "==";
    break;
  case Neq:
    os << "!=";
    break;
  case Lt:
    os << "<";
    break;
  case Gt:
    os << ">";
    break;
  case Lte:
    os << "<=";
    break;
  case Gte:
    os << ">=";
    break;
  case Sub:
    os << "<:";
    break;
  case Conc:
    os << "++";
    break;
  case Plus:
    os << "+";
    break;
  case Minus:
    os << "-";
    break;
  case Times:
    os << "*";
    break;
  case Div:
    os << "/";
    break;
  case Mod:
    os << "%";
    break;
  }
  os << " " << rhs << ")";
}

void FunExpr::print(std::ostream &os) const {
  os << fun;
  print_seq<const Expr *>(os, args, "(", ", ", ")");
}

void BoolLit::print(std::ostream &os) const { os << (val ? "true" : "false"); }

void RModeLit::print(std::ostream &os) const {
  switch (val) {
  case RModeKind::RNE:
    os << "RNE";
    break;
  case RModeKind::RNA:
    os << "RNA";
    break;
  case RModeKind::RTP:
    os << "RTP";
    break;
  case RModeKind::RTN:
    os << "RTN";
    break;
  case RModeKind::RTZ:
    os << "RTZ";
    break;
  }
}

void IntLit::print(std::ostream &os) const { os << val; }

void BvLit::print(std::ostream &os) const { os << val << "bv" << width; }

void FPLit::print(std::ostream &os) const {
  if (specialValue.empty()) {
    os << (neg ? "-" : "") << "0x" << sig << "e" << expo << "f";
  } else {
    os << "0" << specialValue;
  }
  os << sigSize << "e" << expSize;
}

void NegExpr::print(std::ostream &os) const { os << "-(" << expr << ")"; }

void NotExpr::print(std::ostream &os) const { os << "!(" << expr << ")"; }

void QuantExpr::print(std::ostream &os) const {
  os << "(";
  switch (quant) {
  case Forall:
    os << "forall ";
    break;
  case Exists:
    os << "exists ";
    break;
  }
  print_seq<Binding>(os, vars, ", ");
  os << " :: " << expr << ")";
}

void SelExpr::print(std::ostream &os) const {
  os << base;
  print_seq<const Expr *>(os, idxs, "[", ", ", "]");
}

void UpdExpr::print(std::ostream &os) const {
  os << base << "[";
  print_seq<const Expr *>(os, idxs, ", ");
  os << " := " << val << "]";
}

void VarExpr::print(std::ostream &os) const { os << var; }

void CodeExpr::print(std::ostream &os) const {
  os << "|{"
     << "\n";
  if (decls.size() > 0)
    print_seq<Decl *>(os, decls, "  ", "\n  ", "\n");
  print_seq<Block *>(os, blocks, "\n");
  os << "\n"
     << "}|";
}

void IfThenElseExpr::print(std::ostream &os) const {
  os << "(if " << cond << " then " << trueValue << " else " << falseValue
     << ")";
}

void BvExtract::print(std::ostream &os) const {
  os << var << "[" << upper << ":" << lower << "]";
}

void BvConcat::print(std::ostream &os) const {
  os << "(" << left << "++" << right << ")";
}

void StringLit::print(std::ostream &os) const { os << "\"" << val << "\""; }

void Attr::print(std::ostream &os) const {
  os << "{:" << name;
  if (vals.size() > 0)
    print_seq<const Expr *>(os, vals, " ", ", ", "");
  os << "}";
}

void AssertStmt::print(std::ostream &os) const {
  os << "assert ";
  if (attrs.size() > 0)
    print_seq<const Attr *>(os, attrs, "", " ", " ");
  os << expr << ";";
}

void AssignStmt::print(std::ostream &os) const {
  print_seq<const Expr *>(os, lhs, ", ");
  os << " := ";
  print_seq<const Expr *>(os, rhs, ", ");
  os << ";";
}

void AssumeStmt::print(std::ostream &os) const {
  os << "assume ";
  if (attrs.size() > 0)
    print_seq<const Attr *>(os, attrs, "", " ", " ");
  os << expr << ";";
}

void CallStmt::print(std::ostream &os) const {
  os << "call ";
  if (attrs.size() > 0)
    print_seq<const Attr *>(os, attrs, "", " ", " ");
  if (returns.size() > 0)
    print_seq<std::string>(os, returns, "", ", ", " := ");
  os << proc;
  print_seq<const Expr *>(os, params, "(", ", ", ")");
  os << ";";
}

void Comment::print(std::ostream &os) const { os << "/* " << str << " */"; }

void GotoStmt::print(std::ostream &os) const {
  os << "goto ";
  print_seq<std::string>(os, targets, ", ");
  os << ";";
}

void HavocStmt::print(std::ostream &os) const {
  os << "havoc ";
  print_seq<std::string>(os, vars, ", ");
  os << ";";
}

void ReturnStmt::print(std::ostream &os) const {
  os << "return";
  if (expr)
    os << " " << expr;
  os << ";";
}

void CodeStmt::print(std::ostream &os) const { os << code; }

void TypeDecl::print(std::ostream &os) const {
  os << "type ";
  if (attrs.size() > 0)
    print_seq<const Attr *>(os, attrs, "", " ", " ");
  os << name;
  if (alias != "")
    os << " = " << alias;
  os << ";";
}

void AxiomDecl::print(std::ostream &os) const {
  os << "axiom ";
  if (attrs.size() > 0)
    print_seq<const Attr *>(os, attrs, "", " ", " ");
  os << expr << ";";
}

void ConstDecl::print(std::ostream &os) const {
  os << "const ";
  if (attrs.size() > 0)
    print_seq<const Attr *>(os, attrs, "", " ", " ");
  os << (unique ? "unique " : "") << name << ": " << type << ";";
}

void FuncDecl::print(std::ostream &os) const {
  os << "function ";
  if (attrs.size() > 0)
    print_seq<const Attr *>(os, attrs, "", " ", " ");
  os << name << "(";
  for (auto P = params.begin(), E = params.end(); P != E; ++P)
    os << (P == params.begin() ? "" : ", ") << P->first << ": " << P->second;
  os << ") returns (" << type << ")";
  if (body)
    os << " { " << body << " }";
  else
    os << ";";
}

void VarDecl::print(std::ostream &os) const {
  if (attrs.size() > 0)
    print_seq<const Attr *>(os, attrs, "", " ", " ");
  os << "var " << name << ": " << type << ";";
}

void ProcDecl::print(std::ostream &os) const {
  os << "procedure ";
  if (attrs.size() > 0)
    print_seq<const Attr *>(os, attrs, "", " ", " ");
  os << name << "(";
  for (auto P = params.begin(), E = params.end(); P != E; ++P)
    os << (P == params.begin() ? "" : ", ") << P->first << ": " << P->second;
  os << ")";
  if (rets.size() > 0) {
    os << "\n";
    os << "  returns (";
    for (auto R = rets.begin(), E = rets.end(); R != E; ++R)
      os << (R == rets.begin() ? "" : ", ") << R->first << ": " << R->second;
    os << ")";
  }
  if (blocks.size() == 0)
    os << ";";

  if (mods.size() > 0) {
    os << "\n";
    print_seq<std::string>(os, mods, "  modifies ", ", ", ";");
  }
  if (requires.size() > 0) {
    os << "\n";
    print_seq<const Expr *>(os, requires, "  requires ", ";\n  requires ", ";");
  }
  if (ensures.size() > 0) {
    os << "\n";
    print_seq<const Expr *>(os, ensures, "  ensures ", ";\n  ensures ", ";");
  }
  if (blocks.size() > 0) {
    os << "\n";
    os << "{"
       << "\n";
    if (decls.size() > 0)
      print_seq<Decl *>(os, decls, "  ", "\n  ", "\n");
    print_seq<Block *>(os, blocks, "\n");
    os << "\n"
       << "}";
  }
}

void CodeDecl::print(std::ostream &os) const { os << code; }

void Block::print(std::ostream &os) const {
  if (name != "")
    os << name << ":"
       << "\n";
  print_seq<const Stmt *>(os, stmts, "  ", "\n  ", "");
}

void Program::print(std::ostream &os) const {
  os << prelude;
  print_seq<Decl *>(os, decls, "\n");
  os << "\n";
}
} // namespace smack
