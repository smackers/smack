//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BOOGIEAST_H
#define BOOGIEAST_H

#include <cassert>
#include <string>
#include <vector>
#include <set>

namespace smack {

using namespace std;

class Program;

class Expr {
public:
  virtual void print(ostream& os) const = 0;
  static const Expr* exists(string v, string t, const Expr* e);
  static const Expr* forall(string v, string t, const Expr* e);
  static const Expr* and_(const Expr* l, const Expr* r);
  static const Expr* cond(const Expr* c, const Expr* t, const Expr* e);
  static const Expr* eq(const Expr* l, const Expr* r);
  static const Expr* lt(const Expr* l, const Expr* r);
  static const Expr* fn(string f, const Expr* x);
  static const Expr* fn(string f, const Expr* x, const Expr* y);
  static const Expr* fn(string f, const Expr* x, const Expr* y, const Expr* z);
  static const Expr* fn(string f, vector<const Expr*> args);
  static const Expr* id(string x);
  static const Expr* impl(const Expr* l, const Expr* r);
  static const Expr* lit(int i);
  static const Expr* lit(int i, unsigned w);
  static const Expr* lit(bool b);
  static const Expr* neq(const Expr* l, const Expr* r);
  static const Expr* not_(const Expr* e);
  static const Expr* sel(const Expr* b, const Expr* i);
  static const Expr* sel(string b, string i);
};

class BinExpr : public Expr {
public:
  enum Binary { Iff, Imp, Or, And, Eq, Neq, Lt, Gt, Lte, Gte, Sub, Conc,
                Plus, Minus, Times, Div, Mod
              };
private:
  const Binary op;
  const Expr* lhs;
  const Expr* rhs;
public:
  BinExpr(const Binary b, const Expr* l, const Expr* r) : op(b), lhs(l), rhs(r) {}
  void print(ostream& os) const;
};

class CondExpr : public Expr {
  const Expr* cond;
  const Expr* then;
  const Expr* else_;
public:
  CondExpr(const Expr* c, const Expr* t, const Expr* e)
    : cond(c), then(t), else_(e) {}
  void print(ostream& os) const;
};

class FunExpr : public Expr {
  string fun;
  vector<const Expr*> args;
public:
  FunExpr(string f, vector<const Expr*> xs) : fun(f), args(xs) {}
  void print(ostream& os) const;
};

class LitExpr : public Expr {
public:
  enum Literal { True, False, Num, Bv8, Bv32, Bv64 };
private:
  const Literal lit;
  int val;
public:
  LitExpr(bool b) : lit(b ? True : False) {}
  LitExpr(int i) : lit(Num), val(i) {}
  LitExpr(const Literal l, int i) : lit(l), val(i) {}
  void print(ostream& os) const;
};

class NegExpr : public Expr {
  const Expr* expr;
public:
  NegExpr(const Expr* e) : expr(e) {}
  void print(ostream& os) const;
};

class NotExpr : public Expr {
  const Expr* expr;
public:
  NotExpr(const Expr* e) : expr(e) {}
  void print(ostream& os) const;
};

class QuantExpr : public Expr {
public:
  enum Quantifier { Exists, Forall };
private:
  Quantifier quant;
  vector< pair<string,string> > vars;
  const Expr* expr;
public:
  QuantExpr(Quantifier q, vector< pair<string,string> > vs, const Expr* e) : quant(q), vars(vs), expr(e) {}
  void print(ostream& os) const;
};

class SelExpr : public Expr {
  const Expr* base;
  vector<const Expr*> idxs;
public:
  SelExpr(const Expr* a, vector<const Expr*> i) : base(a), idxs(i) {}
  SelExpr(const Expr* a, const Expr* i) : base(a), idxs(vector<const Expr*>(1, i)) {}
  void print(ostream& os) const;
};

class UpdExpr : public Expr {
  const Expr* base;
  vector<const Expr*> idxs;
  const Expr* val;
public:
  UpdExpr(const Expr* a, vector<const Expr*> i, const Expr* v)
    : base(a), idxs(i), val(v) {}
  UpdExpr(const Expr* a, const Expr* i, const Expr* v)
    : base(a), idxs(vector<const Expr*>(1, i)), val(v) {}
  void print(ostream& os) const;
};

class VarExpr : public Expr {
  string var;
public:
  VarExpr(string v) : var(v) {}
  string name() const { return var; }
  void print(ostream& os) const;
};

class AttrVal {
public:
  virtual void print(ostream& os) const = 0;
};

class StrVal : public AttrVal {
  string val;
public:
  StrVal(string s) : val(s) {}
  void print(ostream& os) const;
};

class ExprVal : public AttrVal {
  const Expr* val;
public:
  ExprVal(const Expr* e) : val(e) {}
  void print(ostream& os) const;
};

class Attr {
protected:
  string name;
  vector<const AttrVal*> vals;
public:
  Attr(string n, vector<const AttrVal*> vs) : name(n), vals(vs) {}
  void print(ostream& os) const;

  static const Attr* attr(string s);
  static const Attr* attr(string s, string v);
  static const Attr* attr(string s, int v);
  static const Attr* attr(string s, string v, int i);
  static const Attr* attr(string s, string v, int i, int j);
  static const Attr* attr(string s, vector<const Expr*> vs);
};

class Stmt {
public:
  static const Stmt* annot(vector<const Attr*> attrs);
  static const Stmt* annot(const Attr* a);
  static const Stmt* assert_(const Expr* e);
  static const Stmt* assign(const Expr* e, const Expr* f);
  static const Stmt* assume(const Expr* e);
  static const Stmt* assume(const Expr* e, const Attr* attr);
  static const Stmt* call(string p);
  static const Stmt* call(string p, const Expr* x);
  static const Stmt* call(string p, const Expr* x, const Attr* attr);
  static const Stmt* call(string p, const Expr* x, string r);
  static const Stmt* call(string p, const Expr* x, const Expr* y, string r);
  static const Stmt* call(string p, vector<const Expr*> ps);
  static const Stmt* call(string p, vector<const Expr*> ps, vector<string> rs);
  static const Stmt* call(string p, vector<const Expr*> ps, vector<string> rs, const Attr* attr);
  static const Stmt* call(string p, vector<const Expr*> ps, vector<string> rs, vector<const Attr*> ax);
  static const Stmt* comment(string c);
  static const Stmt* goto_(string t);
  static const Stmt* goto_(string t, string u);
  static const Stmt* goto_(vector<string> ts);
  static const Stmt* havoc(string x);
  static const Stmt* return_();
  static const Stmt* return_(const Expr* e);
  static const Stmt* skip();
  static const Stmt* code(string s);
  virtual void print(ostream& os) const = 0;
};

class AssertStmt : public Stmt {
  const Expr* expr;
public:
  AssertStmt(const Expr* e) : expr(e) {}
  void print(ostream& os) const;
};

class AssignStmt : public Stmt {
  vector<const Expr*> lhs;
  vector<const Expr*> rhs;
public:
  AssignStmt(vector<const Expr*> lhs, vector<const Expr*> rhs) : lhs(lhs), rhs(rhs) {}
  void print(ostream& os) const;
};

class AssumeStmt : public Stmt {
  const Expr* expr;
  vector<const Attr*> attrs;
public:
  AssumeStmt(const Expr* e) : expr(e) {}
  void add(const Attr* a) {
    attrs.push_back(a);
  }
  void print(ostream& os) const;
};

class CallStmt : public Stmt {
  string proc;
  vector<const Expr*> params;
  vector<string> returns;
  vector<const Attr*> attrs;
public:
  CallStmt(string p, vector<const Expr*> ps, vector<string> rs, 
    vector<const Attr*> ax)
    : proc(p), params(ps), returns(rs), attrs(ax) {}
  void print(ostream& os) const;
};

class Comment : public Stmt {
  string str;
public:
  Comment(string s) : str(s) {}
  void print(ostream& os) const;
};

class GotoStmt : public Stmt {
  vector<string> targets;
public:
  GotoStmt(vector<string> ts) : targets(ts) {}
  void print(ostream& os) const;
};

class HavocStmt : public Stmt {
  vector<string> vars;
public:
  HavocStmt(vector<string> vs) : vars(vs) {}
  void print(ostream& os) const;
};

class ReturnStmt : public Stmt {
  const Expr* expr;
public:
  ReturnStmt(const Expr* e = nullptr) : expr(e) {}
  void print(ostream& os) const;
};

class CodeStmt : public Stmt {
  string code;
public:
  CodeStmt(string s) : code(s) {}
  void print(ostream& os) const;
};

class Decl {
  static unsigned uniqueId;
public:
  enum kind { STOR, PROC, FUNC, TYPE, UNNAMED, CODE };
protected:
  unsigned id;
  string name;
  vector<const Attr*> attrs;
  Decl(string n, vector<const Attr*> ax) : id(uniqueId++), name(n), attrs(ax) { }
  Decl(string n) : id(uniqueId++), name(n), attrs(vector<const Attr*>()) { }
public:
  virtual void print(ostream& os) const = 0;
  unsigned getId() const { return id; }
  string getName() const { return name; }
  virtual kind getKind() const = 0;
  void addAttr(const Attr* a) { attrs.push_back(a); }
  
  static Decl* typee(string name, string type);
  static Decl* axiom(const Expr* e);
  static Decl* function(string name, vector< pair<string,string> > args, string type, const Expr* e);
  static Decl* constant(string name, string type);
  static Decl* constant(string name, string type, bool unique);
  static Decl* constant(string name, string type, vector<const Attr*> ax, bool unique);
  static Decl* variable(string name, string type);
  static Decl* procedure(Program& p, string name);
  static Decl* procedure(Program& p, string name,
    vector< pair<string,string> > args, vector< pair<string,string> > rets);
  static Decl* code(string s);
};

struct DeclCompare {
  bool operator()(Decl* a, Decl* b) {
    assert(a && b);    
    if (a->getKind() == b->getKind() && a->getKind() != Decl::UNNAMED)
      return a->getName() < b->getName();
    else if (a->getKind() == b->getKind())
      return a->getId() < b->getId();
    else
      return a->getKind() < b->getKind();
  }
};

class TypeDecl : public Decl {
  string alias;
public:
  TypeDecl(string n, string t) : Decl(n), alias(t) {}
  kind getKind() const { return TYPE; }
  void print(ostream& os) const;
};

class AxiomDecl : public Decl {
  const Expr* expr;
  static int uniqueId;
public:
  AxiomDecl(const Expr* e) : Decl(""), expr(e) {}
  kind getKind() const { return UNNAMED; }
  void print(ostream& os) const;
};

class ConstDecl : public Decl {
  string type;
  bool unique;
public:
  ConstDecl(string n, string t, vector<const Attr*> ax, bool u) : Decl(n,ax), type(t), unique(u) {}
  kind getKind() const { return STOR; }
  void print(ostream& os) const;
};

class FuncDecl : public Decl {
  vector< pair<string, string> > params;
  string type;
  const Expr* body;
public:
  FuncDecl(string n, vector<const Attr*> ax, vector< pair<string, string> > ps,
    string t, const Expr* b)
    : Decl(n,ax), params(ps), type(t), body(b) {}
  kind getKind() const { return FUNC; }
  void print(ostream& os) const;
};

class VarDecl : public Decl {
  string type;
public:
  VarDecl(string n, string t) : Decl(n), type(t) {}
  kind getKind() const { return STOR; }
  void print(ostream& os) const;
};

class Block {
  string name;
  vector<const Stmt*> stmts;
public:
  Block() : name("") {}
  Block(string n) : name(n) {}
  void print(ostream& os) const;
  void insert(const Stmt* s) {
    stmts.insert(stmts.begin(), s);
  }
  void addStmt(const Stmt* s) {
    stmts.push_back(s);
  }
  string getName() {
    return name;
  }
};

class CodeContainer {
protected:
  Program& prog;
  set<Decl*,DeclCompare> decls;
  vector<Block*> blocks;
  vector<string> mods;
  CodeContainer(Program& p) : prog(p) {}
public:
  Program& getProg() const {
    return prog;
  }
  void addDecl(Decl* d) {
    decls.insert(d);
  }
  void insert(const Stmt* s) {
    blocks.front()->insert(s);
  }
  void addBlock(Block* b) {
    blocks.push_back(b);
  }
  bool hasBody() {
    return decls.size() > 0 || blocks.size() > 0;
  }
  void addMod(string m) {
    mods.push_back(m);
  }
  void addMods(vector<string> ms) {
    for (unsigned i = 0; i < ms.size(); i++)
      addMod(ms[i]);
  }
  virtual bool isProc() { return false; }
};

class CodeExpr : public Expr, public CodeContainer {
public:
  CodeExpr(Program& p) : CodeContainer(p) {}
  void print(ostream& os) const;
};

class ProcDecl : public Decl, public CodeContainer {
  vector< pair<string,string> > params;
  vector< pair<string,string> > rets;
  vector<const Expr*> requires;
  vector<const Expr*> ensures;
public:
  ProcDecl(Program& p, string n, vector< pair<string,string> > ps, vector< pair<string,string> > rs) 
    : Decl(n), CodeContainer(p), params(ps), rets(rs) {}
  kind getKind() const { return PROC; }
  void addParam(string x, string t) {
    params.push_back(make_pair(x, t));
  }
  void addRet(string x, string t) {
    rets.push_back(make_pair(x, t));
  }
  vector< pair<string,string> > getRets() {
    return rets;
  }
  void addRequires(const Expr* e) {
    requires.push_back(e);
  }
  void addEnsures(const Expr* e) {
    ensures.push_back(e);
  }
  bool isProc() { return true; }
  void print(ostream& os) const;
};

class CodeDecl : public Decl {
public:
  CodeDecl(string s) : Decl(s) {}
  kind getKind() const { return CODE; }
  void print(ostream& os) const;
};

class Program {
  // TODO While I would prefer that a program is just a set or sequence of
  // declarations, putting the Prelude in a CodeDeclaration does not work,
  // and I do not yet understand why; see below. --mje
  string prelude;
  set<Decl*,DeclCompare> decls;
public:
  Program() {}
  void print(ostream& os) const;
  void addDecl(Decl* d) {
    decls.insert(d);
  }
  void addDecl(string s) {
    // TODO Why does this break to put the prelude string inside of a CodeDecl?
    decls.insert( Decl::code(s) );
  }
  void appendPrelude(string s) {
    prelude += s;
  }
  void addDecls(vector<Decl*> ds) {
    for (unsigned i = 0; i < ds.size(); i++)
      addDecl(ds[i]);
  }
  vector<ProcDecl*> getProcs() {
    vector<ProcDecl*> procs;
    for (set<Decl*>::iterator i = decls.begin(); i != decls.end(); ++i)
      if ((*i)->getKind() == Decl::PROC)
        procs.push_back((ProcDecl*) (*i));
    return procs;
  }
};
}

#endif // BOOGIEAST_H

