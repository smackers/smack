//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/BoogieAst.h"
#include "llvm/IR/Constants.h"
#include <sstream>

namespace smack {

using namespace std;

unsigned Decl::uniqueId = 0;

const Expr* Expr::exists(string v, string t, const Expr* e) {
  vector< pair<string,string> > vars;
  vars.push_back(make_pair(v,t));
  return new QuantExpr(QuantExpr::Exists, vars, e);
}

const Expr* Expr::forall(string v, string t, const Expr* e) {
  vector< pair<string,string> > vars;
  vars.push_back(make_pair(v,t));
  return new QuantExpr(QuantExpr::Forall, vars, e);
}

const Expr* Expr::and_(const Expr* l, const Expr* r) {
  return new BinExpr(BinExpr::And, l, r);
}

const Expr* Expr::cond(const Expr* c, const Expr* t, const Expr* e) {
  return new CondExpr(c,t,e);
}

const Expr* Expr::eq(const Expr* l, const Expr* r) {
  return new BinExpr(BinExpr::Eq, l, r);
}

const Expr* Expr::lt(const Expr* l, const Expr* r) {
  return new BinExpr(BinExpr::Lt, l, r);
}

const Expr* Expr::fn(string f, vector<const Expr*> args) {
  return new FunExpr(f, args);
}

const Expr* Expr::fn(string f, const Expr* x) {
  return new FunExpr(f, vector<const Expr*>(1, x));
}

const Expr* Expr::fn(string f, const Expr* x, const Expr* y) {
  vector<const Expr*> ps;
  ps.push_back(x);
  ps.push_back(y);
  return new FunExpr(f, ps);
}

const Expr* Expr::fn(string f, const Expr* x, const Expr* y, const Expr* z) {
  vector<const Expr*> ps;
  ps.push_back(x);
  ps.push_back(y);
  ps.push_back(z);
  return new FunExpr(f, ps);
}

const Expr* Expr::id(string s) {
  return new VarExpr(s);
}

const Expr* Expr::impl(const Expr* l, const Expr* r) {
  return new BinExpr(BinExpr::Imp, l, r);
}

const Expr* Expr::lit(int i) {
  return new LitExpr(i);
}
const Expr* Expr::lit(int i, unsigned w) {
  switch (w) {
  case 0:
    return new LitExpr(i);
  case 8:
    return new LitExpr(LitExpr::Bv8, i);
  case 32:
    return new LitExpr(LitExpr::Bv32, i);
  case 64:
    return new LitExpr(LitExpr::Bv64, i);
  default:
    assert(false && "unexpected integer width.");
  }
}

const Expr* Expr::lit(bool b) {
  return new LitExpr(b);
}

const Expr* Expr::neq(const Expr* l, const Expr* r) {
  return new BinExpr(BinExpr::Neq, l, r);
}

const Expr* Expr::not_(const Expr* e) {
  return new NotExpr(e);
}

const Expr* Expr::sel(const Expr* b, const Expr* i) {
  return new SelExpr(b, i);
}

const Expr* Expr::sel(string b, string i) {
  return new SelExpr(id(b), id(i));
}

const Attr* Attr::attr(string s, vector<const Expr*> vs) {
  vector<const AttrVal*> vals;
  for (unsigned i=0; i<vs.size(); i++)
    vals.push_back(new ExprVal(vs[i]));
  return new Attr(s,vals);
}

const Attr* Attr::attr(string s) {
  return attr(s, vector<const Expr*>());
}

const Attr* Attr::attr(string s, string v) {
  return new Attr(s, vector<const AttrVal*>(1, new StrVal(v)));
}

const Attr* Attr::attr(string s, int v) {
  return attr(s, vector<const Expr*>(1, Expr::lit(v)));
}

const Attr* Attr::attr(string s, string v, int i) {
  vector<const AttrVal*> vals;
  vals.push_back(new StrVal(v));
  vals.push_back(new ExprVal(Expr::lit(i)));
  return new Attr(s, vals);
}

const Attr* Attr::attr(string s, string v, int i, int j) {
  vector<const AttrVal*> vals;
  vals.push_back(new StrVal(v));
  vals.push_back(new ExprVal(Expr::lit(i)));
  vals.push_back(new ExprVal(Expr::lit(j)));
  return new Attr(s, vals);
}

const Stmt* Stmt::annot(vector<const Attr*> attrs) {
  AssumeStmt* s = new AssumeStmt(Expr::lit(true));
  for (unsigned i = 0; i < attrs.size(); i++)
    s->add(attrs[i]);
  return s;
}

const Stmt* Stmt::annot(const Attr* a) {
  return Stmt::annot(vector<const Attr*>(1, a));
}

const Stmt* Stmt::assert_(const Expr* e) {
  return new AssertStmt(e);
}

const Stmt* Stmt::assign(const Expr* e, const Expr* f) {
  return new AssignStmt(vector<const Expr*>(1, e), vector<const Expr*>(1, f));
}

const Stmt* Stmt::assume(const Expr* e) {
  return new AssumeStmt(e);
}

const Stmt* Stmt::assume(const Expr* e, const Attr* a) {
  AssumeStmt* s = new AssumeStmt(e);
  s->add(a);
  return (const AssumeStmt*) s;
}

const Stmt* Stmt::call(string p) {
  return call(p, vector<const Expr*>(), vector<string>());
}

const Stmt* Stmt::call(string p, const Expr* x) {
  return call(p, vector<const Expr*>(1, x), vector<string>());
}

const Stmt* Stmt::call(string p, const Expr* x, const Attr* attr) {
  return call(p, vector<const Expr*>(1, x), vector<string>(), vector<const Attr*>(1, attr));
}

const Stmt* Stmt::call(string p, const Expr* x, string r) {
  return call(p, vector<const Expr*>(1, x), vector<string>(1, r));
}

const Stmt* Stmt::call(string p, const Expr* x, const Expr* y, string r) {
  vector<const Expr*> ps;
  ps.push_back(x);
  ps.push_back(y);
  return call(p, ps, vector<string>(1, r));
}

const Stmt* Stmt::call(string p, vector<const Expr*> ps) {
  return call(p, ps, vector<string>());
}

const Stmt* Stmt::call(string p, vector<const Expr*> ps, vector<string> rs) {
  return call(p, ps, rs, vector<const Attr*>());
}

const Stmt* Stmt::call(string p, vector<const Expr*> ps, vector<string> rs,
  const Attr* attr) {

  return call(p, ps, rs, vector<const Attr*>(1, attr));
}

const Stmt* Stmt::call(string p, vector<const Expr*> ps, vector<string> rs, 
  vector<const Attr*> ax) {

  return new CallStmt(p, ps, rs, ax);
}

const Stmt* Stmt::comment(string s) {
  return new Comment(s);
}

const Stmt* Stmt::goto_(string t) {
  return goto_(vector<string>(1, t));
}

const Stmt* Stmt::goto_(string t, string u) {
  vector<string> ts(2, "");
  ts[0] = t;
  ts[1] = u;
  return goto_(ts);
}

const Stmt* Stmt::goto_(vector<string> ts) {
  return new GotoStmt(ts);
}

const Stmt* Stmt::havoc(string x) {
  return new HavocStmt(vector<string>(1, x));
}

const Stmt* Stmt::return_(const Expr* e) {
  return new ReturnStmt(e);
}

const Stmt* Stmt::return_() {
  return new ReturnStmt();
}

const Stmt* Stmt::skip() {
  return new AssumeStmt(Expr::lit(true));
}

const Stmt* Stmt::code(string s) {
  return new CodeStmt(s);
}

Decl* Decl::typee(string name, string type) {
  return new TypeDecl(name,type);
}
Decl* Decl::axiom(const Expr* e) {
  return new AxiomDecl(e);
}
Decl* Decl::function(string name, vector< pair<string,string> > args, string type, const Expr* e) {
  return new FuncDecl(name,vector<const Attr*>(),args,type,e);
}
Decl* Decl::constant(string name, string type) {
  return Decl::constant(name, type, vector<const Attr*>(), false);
}
Decl* Decl::constant(string name, string type, bool unique) {
  return Decl::constant(name, type, vector<const Attr*>(), unique);
}
Decl* Decl::constant(string name, string type, vector<const Attr*> ax, bool unique) {
  return new ConstDecl(name, type, ax, unique);
}
Decl* Decl::variable(string name, string type) {
  return new VarDecl(name, type);
}
Decl* Decl::procedure(Program& p, string name) {
  return procedure(p,name,vector< pair<string,string> >(),vector< pair<string,string> >());
}
Decl* Decl::procedure(Program& p, string name, 
    vector< pair<string,string> > args, vector< pair<string,string> > rets) {
  return new ProcDecl(p,name,args,rets);
}
Decl* Decl::code(string s) {
  return new CodeDecl(s);
}

ostream& operator<<(ostream& os, const Expr& e) {
  e.print(os);
  return os;
}
ostream& operator<<(ostream& os, const Expr* e) {
  e->print(os);
  return os;
}
ostream& operator<<(ostream& os, const AttrVal* v) {
  v->print(os);
  return os;
}
ostream& operator<<(ostream& os, const Attr* a) {
  a->print(os);
  return os;
}
ostream& operator<<(ostream& os, const Stmt* s) {
  s->print(os);
  return os;
}
ostream& operator<<(ostream& os, const Block* b) {
  b->print(os);
  return os;
}
ostream& operator<<(ostream& os, Decl* d) {
  d->print(os);
  return os;
}
ostream& operator<<(ostream& os, Program* p) {
  if (p == 0) {
    os << "<null> Program!\n";
  } else {
    p->print(os);
  }
  return os;
}
ostream& operator<<(ostream& os, Program& p) {
  p.print(os);
  return os;
}

template<class T,class U> ostream& operator<<(ostream& os, pair<T,U> p) {
  os << p.first << ": " << p.second;
  return os;
}

template<class T> void print_seq(ostream& os, vector<T> ts,
                                 string init, string sep, string term) {

  os << init;
  for (typename vector<T>::iterator i = ts.begin(); i != ts.end(); ++i)
    os << (i == ts.begin() ? "" : sep) << *i;
  os << term;
}
template<class T> void print_seq(ostream& os, vector<T> ts, string sep) {
  print_seq<T>(os, ts, "", sep, "");
}
template<class T> void print_seq(ostream& os, vector<T> ts) {
  print_seq<T>(os, ts, "", "", "");
}
template<class T, class C> void print_set(ostream& os, set<T,C> ts,
                                 string init, string sep, string term) {

  os << init;
  for (typename set<T,C>::iterator i = ts.begin(); i != ts.end(); ++i)
    os << (i == ts.begin() ? "" : sep) << *i;
  os << term;
}
template<class T, class C> void print_set(ostream& os, set<T,C> ts, string sep) {
  print_set<T,C>(os, ts, "", sep, "");
}
template<class T, class C> void print_set(ostream& os, set<T,C> ts) {
  print_set<T,C>(os, ts, "", "", "");
}

void BinExpr::print(ostream& os) const {
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

void CondExpr::print(ostream& os) const {
  os << "if " << cond << " then " << then << " else " << else_;
}

void FunExpr::print(ostream& os) const {
  os << fun;
  print_seq<const Expr*>(os, args, "(", ", ", ")");
}

void LitExpr::print(ostream& os) const {
  switch (lit) {
  case True:
    os << "true";
    break;
  case False:
    os << "false";
    break;
  case Num:
    os << val;
    break;
  case Bv8:
    os << val << "bv8";
    break;
  case Bv32:
    os << val << "bv32";
    break;
  case Bv64:
    os << val << "bv64";
    break;
  }
}

void NegExpr::print(ostream& os) const {
  os << "-(" << expr << ")";
}

void NotExpr::print(ostream& os) const {
  os << "!(" << expr << ")";
}

void QuantExpr::print(ostream& os) const {
  os << "(";
  switch (quant) {
  case Forall:
    os << "forall ";
    break;
  case Exists:
    os << "exists ";
    break;
  }
  print_seq< pair<string,string> >(os, vars, ",");
  os << " :: " << expr << ")";
}

void SelExpr::print(ostream& os) const {
  os << base;
  print_seq<const Expr*>(os, idxs, "[", ", ", "]");
}

void UpdExpr::print(ostream& os) const {
  os << base << "[";
  print_seq<const Expr*>(os, idxs, ", ");
  os << " := " << val << "]";
}

void VarExpr::print(ostream& os) const {
  os << var;
}

void CodeExpr::print(ostream& os) const {
  os << "|{" << endl;
  if (decls.size() > 0)
    print_set<Decl*>(os, decls, "  ", "\n  ", "\n");
  print_seq<Block*>(os, blocks, "\n");
  os << endl << "}|";
}

void StrVal::print(ostream& os) const {
  os << "\"" << val << "\"";
}

void ExprVal::print(ostream& os) const {
  os << val;
}

void Attr::print(ostream& os) const {
  os << "{:" << name;
  if (vals.size() > 0)
    print_seq<const AttrVal*>(os, vals, " ", ", ", "");
  os << "}";
}

void AssertStmt::print(ostream& os) const {
  os << "assert " << expr << ";";
}

void AssignStmt::print(ostream& os) const {
  print_seq<const Expr*>(os, lhs, ", ");
  os << " := ";
  print_seq<const Expr*>(os, rhs, ", ");
  os << ";";
}

void AssumeStmt::print(ostream& os) const {
  os << "assume ";
  if (attrs.size() > 0)
    print_seq<const Attr*>(os, attrs, "", " ", " ");
  os << expr << ";";
}

void CallStmt::print(ostream& os) const {
  os << "call ";
  if (attrs.size() > 0)
    print_seq<const Attr*>(os, attrs, "", " ", " ");
  if (returns.size() > 0)
    print_seq<string>(os, returns, "", ", ", " := ");
  os << proc;
  print_seq<const Expr*>(os, params, "(", ", ", ")");
  os << ";";
}

void Comment::print(ostream& os) const {
  os << "// " << str;
}

void GotoStmt::print(ostream& os) const {
  os << "goto ";
  print_seq<string>(os, targets, ", ");
  os << ";";
}

void HavocStmt::print(ostream& os) const {
  os << "havoc ";
  print_seq<string>(os, vars, ", ");
  os << ";";
}

void ReturnStmt::print(ostream& os) const {
  os << "return";
  if (expr)
    os << " " << expr;  
  os << ";";
}

void CodeStmt::print(ostream& os) const {
  os << code;
}

void TypeDecl::print(ostream& os) const {
  os << "type ";
  if (attrs.size() > 0)
    print_seq<const Attr*>(os, attrs, "", " ", " ");
  os << name;
  if (alias != "")
    os << " = " << alias << ";";
  os << ";";
}

void AxiomDecl::print(ostream& os) const {
  os << "axiom ";
  if (attrs.size() > 0)
    print_seq<const Attr*>(os, attrs, "", " ", " ");
  os << expr << ";";
}

void ConstDecl::print(ostream& os) const {
  os << "const ";
  if (attrs.size() > 0)
    print_seq<const Attr*>(os, attrs, "", " ", " ");
  os << (unique ? "unique " : "") << name << ": " << type << ";";
}

void FuncDecl::print(ostream& os) const {
  os << "function ";
  if (attrs.size() > 0)
    print_seq<const Attr*>(os, attrs, "", " ", " ");
  os << name << "(";
  for (unsigned i = 0; i < params.size(); i++)
    os << params[i].first << ": " << params[i].second
       << (i < params.size() - 1 ? ", " : "");
  os << ") returns (" << type << ")";
  if (body)
    os << " { " << body << " }";
  else
    os << ";";
}

void VarDecl::print(ostream& os) const {
  if (attrs.size() > 0)
    print_seq<const Attr*>(os, attrs, "", " ", " ");
  os << "var " << name << ": " << type << ";";
}

void ProcDecl::print(ostream& os) const {
  os << "procedure ";
  if (attrs.size() > 0)
    print_seq<const Attr*>(os, attrs, "", " ", " ");
  os << name << "(";
  for (unsigned i = 0; i < params.size(); i++)
    os << params[i].first << ": " << params[i].second
       << (i < params.size() - 1 ? ", " : "");
  os << ")";
  if (rets.size() > 0) {
    os << endl;
    os << "  returns (";
    for (unsigned i = 0; i < rets.size(); i++)
      os << rets[i].first << ": " << rets[i].second
         << (i < rets.size() - 1 ? ", " : "");
    os << ")";
  }
  if (blocks.size() == 0)
    os << ";";

  if (mods.size() > 0) {
    os << endl;
    print_seq<string>(os, mods, "  modifies ", ", ", ";");
  }
  if (requires.size() > 0) {
    os << endl;
    print_seq<const Expr*>(os, requires, "  requires ", ";\n  requires ", ";");
  }
  if (ensures.size() > 0) {
    os << endl;
    print_seq<const Expr*>(os, ensures, "  ensures ", ";\n  ensures ", ";");
  }
  if (blocks.size() > 0) {
    os << endl;
    os << "{" << endl;
    if (decls.size() > 0)
      print_set<Decl*>(os, decls, "  ", "\n  ", "\n");
    print_seq<Block*>(os, blocks, "\n");
    os << endl << "}";
  }
}

void CodeDecl::print(ostream& os) const {
  os << name;
}

void Block::print(ostream& os) const {
  if (name != "")
    os << name << ":" << endl;
  print_seq<const Stmt*>(os, stmts, "  ", "\n  ", "");
}

void Program::print(ostream& os) const {
  os << "// BEGIN SMACK-GENERATED CODE" << endl;
  os << prelude;
  print_set<Decl*>(os, decls, "\n");
  os << endl;
  os << endl;
  os << "// END SMACK-GENERATED CODE" << endl;
}
}

