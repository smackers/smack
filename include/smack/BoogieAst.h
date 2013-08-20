//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BOOGIEAST_H
#define BOOGIEAST_H

#include <string>
#include <vector>

namespace smack {

using namespace std;

class Expr {
public:
  virtual void print(ostream& os) const = 0;
  static const Expr* and_(const Expr* l, const Expr* r);
  static const Expr* eq(const Expr* l, const Expr* r);
  static const Expr* fn(string f, const Expr* x);
  static const Expr* fn(string f, const Expr* x, const Expr* y);
  static const Expr* fn(string f, const Expr* x, const Expr* y, const Expr* z);
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
  int width;
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
  enum Quantifier { Forall, Exists };
private:
  Quantifier q;
public:
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
};

class Stmt {
public:
  static const Stmt* annot(vector<const Attr*> attrs);
  static const Stmt* annot(const Attr* a);
  static const Stmt* assert_(const Expr* e);
  static const Stmt* assign(const Expr* e, const Expr* f);
  static const Stmt* assume(const Expr* e);
  static const Stmt* call(string p, const Expr* x);
  static const Stmt* call(string p, const Expr* x, string r);
  static const Stmt* call(string p, const Expr* x, const Expr* y, string r);
  static const Stmt* call(string p, vector<const Expr*> ps);
  static const Stmt* call(string p, vector<const Expr*> ps, vector<string> rs);
  static const Stmt* comment(string c);
  static const Stmt* goto_(string t);
  static const Stmt* goto_(string t, string u);
  static const Stmt* goto_(vector<string> ts);
  static const Stmt* havoc(string x);
  static const Stmt* return_();
  static const Stmt* skip();
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
public:
  CallStmt(string p, vector<const Expr*> ps, vector<string> rs)
    : proc(p), params(ps), returns(rs) {}
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
public:
  ReturnStmt() {}
  void print(ostream& os) const;
};

class Decl {
protected:
  string name;
  string type;
  Decl(string n, string t) : name(n), type(t) {}
public:
  virtual void print(ostream& os) const = 0;
  string getName() const {
    return name;
  }
  string getType() const {
    return type;
  }
  static const Decl* typee(string name, string type);
  static const Decl* axiom(const Expr* e);
  static const Decl* constant(string name, string type);
  static const Decl* constant(string name, string type, bool unique);
  static const Decl* variable(string name, string type);
  static const Decl* procedure(string name, string arg, string type);
};

class TypeDecl : public Decl {
public:
  TypeDecl(string n, string t) : Decl(n,t) {}
  void print(ostream& os) const;
};

class AxiomDecl : public Decl {
  const Expr* expr;
public:
  AxiomDecl(const Expr* e) : Decl("", ""), expr(e) {}
  void print(ostream& os) const;
};

class ConstDecl : public Decl {
  bool unique;
public:
  ConstDecl(string n, string t, bool u) : Decl(n, t), unique(u) {}
  ConstDecl(string n, string t) : Decl(n, t), unique(false) {}
  void print(ostream& os) const;
};

class FuncDecl : public Decl {
  vector< pair<string, string> > params;
  const Expr* body;
public:
  FuncDecl(string n, vector< pair<string, string> > ps, string t, Expr* b)
    : Decl(n, ""), params(ps), body(b) {}
  void print(ostream& os) const;
};

class VarDecl : public Decl {
public:
  VarDecl(string n, string t) : Decl(n, t) {}
  void print(ostream& os) const;
};

class ProcDecl : public Decl {
  vector< pair<string,string> > params;
public:
  ProcDecl(string n, vector< pair<string,string> > ps, string r) 
    : Decl(n,r), params(ps) {}
  void print(ostream& os) const;
};

class Block {
  string name;
  vector<const Stmt*> stmts;
public:
  Block() : name("") {}
  Block(string n) : name(n) {}
  void print(ostream& os) const;
  void addStmt(const Stmt* s) {
    stmts.push_back(s);
  }
  string getName() {
    return name;
  }
};

class Procedure {
  string name;
  vector< pair<string, string> > params;
  vector< pair<string, string> > rets;
  vector<string> mods;
  vector<const Decl*> decls;
  vector<Block*> blocks;
public:
  Procedure(string n) : name(n) {}
  void print(ostream& os) const;
  void addParam(string x, string t) {
    params.push_back(make_pair(x, t));
  }
  void addRet(string x, string t) {
    rets.push_back(make_pair(x, t));
  }
  void addMod(string m) {
    mods.push_back(m);
  }
  void addMods(vector<string> ms) {
    for (unsigned i = 0; i < ms.size(); i++)
      addMod(ms[i]);
  }
  void addDecl(const Decl* d) {
    decls.push_back(d);
  }
  void addDecls(vector<const Decl*> ds) {
    for (unsigned i = 0; i < ds.size(); i++)
      addDecl(ds[i]);
  }
  bool hasDecl(const Decl* d) {
    for (unsigned i = 0; i < decls.size(); i++)
      if (d->getName() == decls[i]->getName()
          && d->getType() == decls[i]->getType())
        return true;
    return false;
  }
  void addBlock(Block* b) {
    blocks.push_back(b);
  }
};

class Program {
  string prelude;
  vector<const Decl*> decls;
  vector<Procedure*> procs;
public:
  Program(string p) : prelude(p) { }
  void print(ostream& os) const;
  void addDecl(const Decl* d) {
    decls.push_back(d);
  }
  void addDecls(vector<const Decl*> ds) {
    for (unsigned i = 0; i < ds.size(); i++)
      addDecl(ds[i]);
  }
  void addProc(Procedure* p) {
    procs.push_back(p);
  }
  vector<Procedure*>::const_iterator pbegin() {
    return procs.begin();
  }
  vector<Procedure*>::const_iterator pend() {
    return procs.end();
  }
  void appendPrelude(string s) {
    prelude += s;
  }
};
}

#endif // BOOGIEAST_H

