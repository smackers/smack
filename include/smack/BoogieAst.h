//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BOOGIEAST_H
#define BOOGIEAST_H

#include <sstream>
#include <string>
#include <list>

namespace smack {

class Expr {
public:
  virtual ~Expr() {}
  virtual void print(std::ostream& os) const = 0;
  static const Expr* exists(std::string v, std::string t, const Expr* e);
  static const Expr* forall(std::string v, std::string t, const Expr* e);
  static const Expr* and_(const Expr* l, const Expr* r);
  static const Expr* cond(const Expr* c, const Expr* t, const Expr* e);
  static const Expr* eq(const Expr* l, const Expr* r);
  static const Expr* lt(const Expr* l, const Expr* r);
  static const Expr* fn(std::string f, const Expr* x);
  static const Expr* fn(std::string f, const Expr* x, const Expr* y);
  static const Expr* fn(std::string f, const Expr* x, const Expr* y, const Expr* z);
  static const Expr* fn(std::string f, std::list<const Expr*> args);
  static const Expr* id(std::string x);
  static const Expr* impl(const Expr* l, const Expr* r);
  static const Expr* lit(bool b);
  static const Expr* lit(std::string v);
  static const Expr* lit(unsigned v) { return lit((unsigned long) v); }
  static const Expr* lit(unsigned long v);
  static const Expr* lit(long v);
  static const Expr* lit(std::string v, unsigned w);
  static const Expr* lit(unsigned long v, unsigned w);
  static const Expr* lit(bool n, std::string s, std::string e, unsigned ss, unsigned es);
  static const Expr* neq(const Expr* l, const Expr* r);
  static const Expr* not_(const Expr* e);
  static const Expr* sel(const Expr* b, const Expr* i);
  static const Expr* sel(std::string b, std::string i);
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
  void print(std::ostream& os) const;
};

class CondExpr : public Expr {
  const Expr* cond;
  const Expr* then;
  const Expr* else_;
public:
  CondExpr(const Expr* c, const Expr* t, const Expr* e)
    : cond(c), then(t), else_(e) {}
  void print(std::ostream& os) const;
};

class FunExpr : public Expr {
  std::string fun;
  std::list<const Expr*> args;
public:
  FunExpr(std::string f, std::list<const Expr*> xs) : fun(f), args(xs) {}
  void print(std::ostream& os) const;
};

class BoolLit : public Expr {
  bool val;
public:
  BoolLit(bool b) : val(b) {}
  void print(std::ostream& os) const;
};

class IntLit : public Expr {
  std::string val;
public:
  IntLit(std::string v) : val(v) {}
  IntLit(unsigned long v) {
    std::stringstream s;
    s << v;
    val = s.str();
  }
  IntLit(long v) {
    std::stringstream s;
    s << v;
    val = s.str();
  }
  void print(std::ostream& os) const;
};

class BvLit : public Expr {
  std::string val;
  unsigned width;
public:
  BvLit(std::string v, unsigned w) : val(v), width(w) {}
  BvLit(unsigned long v, unsigned w) : width(w) {
    std::stringstream s;
    s << v;
    val = s.str();
  }
  void print(std::ostream& os) const;
};

class FPLit : public Expr {
  bool neg;
  std::string sig;
  std::string expo;
  unsigned sigSize;
  unsigned expSize;
public:
  FPLit(bool n, std::string s, std::string e, unsigned ss, unsigned es) : neg(n), sig(s), expo(e), sigSize(ss), expSize(es) {}
  void print(std::ostream& os) const;
};

class StringLit : public Expr {
  std::string val;
public:
  StringLit(std::string v) : val(v) {}
  void print(std::ostream& os) const;
};

class NegExpr : public Expr {
  const Expr* expr;
public:
  NegExpr(const Expr* e) : expr(e) {}
  void print(std::ostream& os) const;
};

class NotExpr : public Expr {
  const Expr* expr;
public:
  NotExpr(const Expr* e) : expr(e) {}
  void print(std::ostream& os) const;
};

class QuantExpr : public Expr {
public:
  enum Quantifier { Exists, Forall };
private:
  Quantifier quant;
  std::list< std::pair<std::string,std::string> > vars;
  const Expr* expr;
public:
  QuantExpr(Quantifier q, std::list< std::pair<std::string,std::string> > vs, const Expr* e) : quant(q), vars(vs), expr(e) {}
  void print(std::ostream& os) const;
};

class SelExpr : public Expr {
  const Expr* base;
  std::list<const Expr*> idxs;
public:
  SelExpr(const Expr* a, std::list<const Expr*> i) : base(a), idxs(i) {}
  SelExpr(const Expr* a, const Expr* i) : base(a), idxs(std::list<const Expr*>(1, i)) {}
  void print(std::ostream& os) const;
};

class UpdExpr : public Expr {
  const Expr* base;
  std::list<const Expr*> idxs;
  const Expr* val;
public:
  UpdExpr(const Expr* a, std::list<const Expr*> i, const Expr* v)
    : base(a), idxs(i), val(v) {}
  UpdExpr(const Expr* a, const Expr* i, const Expr* v)
    : base(a), idxs(std::list<const Expr*>(1, i)), val(v) {}
  void print(std::ostream& os) const;
};

class VarExpr : public Expr {
  std::string var;
public:
  VarExpr(std::string v) : var(v) {}
  std::string name() const { return var; }
  void print(std::ostream& os) const;
};

class Attr {
protected:
  std::string name;
  std::list<const Expr*> vals;
public:
  Attr(std::string n, std::initializer_list<const Expr*> vs) : name(n), vals(vs) {}
  Attr(std::string n, std::list<const Expr*> vs) : name(n), vals(vs) {}
  void print(std::ostream& os) const;
  std::string getName() const { return name; }

  static const Attr* attr(std::string s);
  static const Attr* attr(std::string s, std::string v);
  static const Attr* attr(std::string s, int v);
  static const Attr* attr(std::string s, std::string v, int i);
  static const Attr* attr(std::string s, std::string v, int i, int j);
  static const Attr* attr(std::string s, std::initializer_list<const Expr*> vs);
  static const Attr* attr(std::string s, std::list<const Expr*> vs);
};

class Stmt {
public:
  enum Kind {
    ASSERT, ASSUME, ASSIGN, HAVOC, GOTO, CALL, RETURN, CODE, COMMENT
  };
private:
  const Kind kind;
protected:
  Stmt(Kind k) : kind(k) {}
public:
  Kind getKind() const { return kind; }

 public:
  virtual ~Stmt() {}
  static const Stmt* annot(std::list<const Attr*> attrs);
  static const Stmt* annot(const Attr* a);
  static const Stmt* assert_(const Expr* e,
    std::list<const Attr*> attrs = std::list<const Attr*>());
  static const Stmt* assign(const Expr* e, const Expr* f);
  static const Stmt* assign(std::list<const Expr*> lhs, std::list<const Expr*> rhs);
  static const Stmt* assume(const Expr* e);
  static const Stmt* assume(const Expr* e, const Attr* attr);
  static const Stmt* call(
    std::string p,
    std::list<const Expr*> args = std::list<const Expr*>(),
    std::list<std::string> rets = std::list<std::string>(),
    std::list<const Attr*> attrs = std::list<const Attr*>());
  static const Stmt* comment(std::string c);
  static const Stmt* goto_(std::list<std::string> ts);
  static const Stmt* havoc(std::string x);
  static const Stmt* return_();
  static const Stmt* return_(const Expr* e);
  static const Stmt* skip();
  static const Stmt* code(std::string s);
  virtual void print(std::ostream& os) const = 0;
};

class AssertStmt : public Stmt {
  const Expr* expr;
  std::list<const Attr*> attrs;
public:
  AssertStmt(const Expr* e, std::list<const Attr*> ax)
    : Stmt(ASSERT), expr(e), attrs(ax) {}
  void print(std::ostream& os) const;
  static bool classof(const Stmt* S) { return S->getKind() == ASSERT; }
};

class AssignStmt : public Stmt {
  std::list<const Expr*> lhs;
  std::list<const Expr*> rhs;
public:
  AssignStmt(std::list<const Expr*> lhs, std::list<const Expr*> rhs)
    : Stmt(ASSIGN), lhs(lhs), rhs(rhs) {}
  void print(std::ostream& os) const;
  static bool classof(const Stmt* S) { return S->getKind() == ASSIGN; }
};

class AssumeStmt : public Stmt {
  const Expr* expr;
  std::list<const Attr*> attrs;
public:
  AssumeStmt(const Expr* e) : Stmt(ASSUME), expr(e) {}
  void add(const Attr* a) {
    attrs.push_back(a);
  }
  bool hasAttr(std::string name) const {
    for (auto a = attrs.begin(); a != attrs.end(); ++a) {
      if ((*a)->getName() == name)
        return true;
    }
    return false;
  }
  void print(std::ostream& os) const;
  static bool classof(const Stmt* S) { return S->getKind() == ASSUME; }
};

class CallStmt : public Stmt {
  std::string proc;
  std::list<const Attr*> attrs;
  std::list<const Expr*> params;
  std::list<std::string> returns;
public:
  CallStmt(std::string p,
    std::list<const Attr*> attrs,
    std::list<const Expr*> args,
    std::list<std::string> rets)
    : Stmt(CALL), proc(p), attrs(attrs), params(args), returns(rets) {}

  void print(std::ostream& os) const;
  static bool classof(const Stmt* S) { return S->getKind() == CALL; }
};

class Comment : public Stmt {
  std::string str;
public:
  Comment(std::string s) : Stmt(COMMENT), str(s) {}
  void print(std::ostream& os) const;
  static bool classof(const Stmt* S) { return S->getKind() == COMMENT; }
};

class GotoStmt : public Stmt {
  std::list<std::string> targets;
public:
  GotoStmt(std::list<std::string> ts) : Stmt(GOTO), targets(ts) {}
  void print(std::ostream& os) const;
  static bool classof(const Stmt* S) { return S->getKind() == GOTO; }
};

class HavocStmt : public Stmt {
  std::list<std::string> vars;
public:
  HavocStmt(std::list<std::string> vs) : Stmt(HAVOC), vars(vs) {}
  void print(std::ostream& os) const;
  static bool classof(const Stmt* S) { return S->getKind() == HAVOC; }
};

class ReturnStmt : public Stmt {
  const Expr* expr;
public:
  ReturnStmt(const Expr* e = nullptr) : Stmt(RETURN), expr(e) {}
  void print(std::ostream& os) const;
  static bool classof(const Stmt* S) { return S->getKind() == RETURN; }
};

class CodeStmt : public Stmt {
  std::string code;
public:
  CodeStmt(std::string s) : Stmt(CODE), code(s) {}
  void print(std::ostream& os) const;
  static bool classof(const Stmt* S) { return S->getKind() == CODE; }
};

class Block;
class ProcDecl;
class FuncDecl;

class Decl {
public:
  enum Kind {
    CONSTANT, VARIABLE, PROCEDURE, FUNCTION, TYPE, AXIOM, CODE
  };
private:
  const Kind kind;
public:
  Kind getKind() const { return kind; }
private:
  static unsigned uniqueId;
protected:
  unsigned id;
  std::string name;
  std::list<const Attr*> attrs;
  Decl(Kind k, std::string n, std::list<const Attr*> ax)
    : kind(k), id(uniqueId++), name(n), attrs(ax) { }
public:
  virtual ~Decl() {}
  virtual void print(std::ostream& os) const = 0;
  unsigned getId() const { return id; }
  std::string getName() const { return name; }
  void addAttr(const Attr* a) { attrs.push_back(a); }

  static Decl* typee(std::string name, std::string type);
  static Decl* axiom(const Expr* e);
  static FuncDecl* function(
    std::string name,
    std::list< std::pair<std::string,std::string> > args,
    std::string type,
    const Expr* e = NULL,
    std::list<const Attr*> attrs = std::list<const Attr*>());
  static Decl* constant(std::string name, std::string type);
  static Decl* constant(std::string name, std::string type, bool unique);
  static Decl* constant(std::string name, std::string type, std::list<const Attr*> ax, bool unique);
  static Decl* variable(std::string name, std::string type);
  static ProcDecl* procedure(std::string name,
    std::list< std::pair<std::string,std::string> > params = std::list< std::pair<std::string,std::string> >(),
    std::list< std::pair<std::string,std::string> > rets = std::list< std::pair<std::string,std::string> >(),
    std::list<Decl*> decls = std::list<Decl*>(),
    std::list<Block*> blocks = std::list<Block*>());
  static Decl* code(std::string name, std::string s);
  static FuncDecl* code(ProcDecl* P);
};

class TypeDecl : public Decl {
  std::string alias;
public:
  TypeDecl(std::string n, std::string t) : Decl(TYPE, n, {}), alias(t) {}
  void print(std::ostream& os) const;
  static bool classof(const Decl* D) { return D->getKind() == TYPE; }
};

class AxiomDecl : public Decl {
  const Expr* expr;
  static int uniqueId;
public:
  AxiomDecl(const Expr* e) : Decl(AXIOM, "", {}), expr(e) {}
  void print(std::ostream& os) const;
  static bool classof(const Decl* D) { return D->getKind() == AXIOM; }
};

class ConstDecl : public Decl {
  std::string type;
  bool unique;
public:
  ConstDecl(std::string n, std::string t, std::list<const Attr*> ax, bool u)
    : Decl(CONSTANT, n, ax), type(t), unique(u) {}
  void print(std::ostream& os) const;
  static bool classof(const Decl* D) { return D->getKind() == CONSTANT; }
};

class FuncDecl : public Decl {
  std::list< std::pair<std::string, std::string> > params;
  std::string type;
  const Expr* body;
public:
  FuncDecl(std::string n, std::list<const Attr*> ax, std::list< std::pair<std::string, std::string> > ps,
    std::string t, const Expr* b)
    : Decl(FUNCTION, n, ax), params(ps), type(t), body(b) {}
  void print(std::ostream& os) const;
  static bool classof(const Decl* D) { return D->getKind() == FUNCTION; }
};

class VarDecl : public Decl {
  std::string type;
public:
  VarDecl(std::string n, std::string t) : Decl(VARIABLE, n, {}), type(t) {}
  void print(std::ostream& os) const;
  static bool classof(const Decl* D) { return D->getKind() == VARIABLE; }
};

class Block {
  std::string name;
  typedef std::list<const Stmt*> StatementList;
  StatementList stmts;
public:
  static Block* block(std::string n = "", std::list<const Stmt*> stmts = std::list<const Stmt*>()) {
    return new Block(n,stmts);
  }
  Block(std::string n, std::list<const Stmt*> stmts) : name(n), stmts(stmts) {}
  void print(std::ostream& os) const;
  typedef StatementList::iterator iterator;
  iterator begin() { return stmts.begin(); }
  iterator end() { return stmts.end(); }
  StatementList &getStatements() { return stmts; }
  void insert(const Stmt* s) {
    stmts.insert(stmts.begin(), s);
  }
  void addStmt(const Stmt* s) {
    stmts.push_back(s);
  }
  std::string getName() {
    return name;
  }
};

class CodeContainer {
protected:
  typedef std::list<Decl*> DeclarationList;
  typedef std::list<Block*> BlockList;
  typedef std::list<std::string> ModifiesList;
  DeclarationList decls;
  BlockList blocks;
  ModifiesList mods;
  CodeContainer(DeclarationList ds, BlockList bs) : decls(ds), blocks(bs) {}
public:
  typedef DeclarationList::iterator decl_iterator;
  decl_iterator decl_begin() { return decls.begin(); }
  decl_iterator decl_end() { return decls.end(); }
  DeclarationList& getDeclarations() { return decls; }

  typedef BlockList::iterator iterator;
  iterator begin() { return blocks.begin(); }
  iterator end() { return blocks.end(); }
  BlockList& getBlocks() { return blocks; }

  typedef ModifiesList::iterator mod_iterator;
  mod_iterator mod_begin() { return mods.begin(); }
  mod_iterator mod_end() { return mods.end(); }
  ModifiesList& getModifies() { return mods; }

  void insert(const Stmt* s) {
    blocks.front()->insert(s);
  }
};

class CodeExpr : public Expr, public CodeContainer {
public:
  CodeExpr(DeclarationList ds, BlockList bs) : CodeContainer(ds, bs) {}
  void print(std::ostream& os) const;
};

class ProcDecl : public Decl, public CodeContainer {
  typedef std::pair<std::string,std::string> Parameter;
  typedef std::list<Parameter> ParameterList;
  typedef std::list<const Expr*> SpecificationList;

  ParameterList params;
  ParameterList rets;
  SpecificationList requires;
  SpecificationList ensures;
public:
  ProcDecl(std::string n, ParameterList ps, ParameterList rs,
    DeclarationList ds, BlockList bs)
    : Decl(PROCEDURE, n, {}), CodeContainer(ds, bs), params(ps), rets(rs) {}
  typedef ParameterList::iterator param_iterator;
  param_iterator param_begin() { return params.begin(); }
  param_iterator param_end() { return params.end(); }
  ParameterList &getParameters() { return params; }

  param_iterator returns_begin() { return rets.begin(); }
  param_iterator returns_end() { return rets.end(); }
  ParameterList &getReturns() { return rets; }

  typedef SpecificationList::iterator spec_iterator;
  spec_iterator requires_begin() { return requires.begin(); }
  spec_iterator requires_end() { return requires.end(); }
  SpecificationList &getRequires() { return requires; }

  spec_iterator ensures_begin() { return ensures.begin(); }
  spec_iterator ensures_end() { return ensures.end(); }
  SpecificationList &getEnsures() { return ensures; }

  void print(std::ostream& os) const;
  static bool classof(const Decl* D) { return D->getKind() == PROCEDURE; }
};

class CodeDecl : public Decl {
  std::string code;
public:
  CodeDecl(std::string name, std::string s) : Decl(CODE, name, {}), code(s) {}
  void print(std::ostream& os) const;
  static bool classof(const Decl* D) { return D->getKind() == CODE; }
};

class Program {
  // TODO While I would prefer that a program is just a set or sequence of
  // declarations, putting the Prelude in a CodeDeclaration does not work,
  // and I do not yet understand why; see below. --mje
  std::string prelude;
  typedef std::list<Decl*> DeclarationList;
  DeclarationList decls;
public:
  Program() {}
  void print(std::ostream& os) const;
  typedef DeclarationList::iterator iterator;
  iterator begin() { return decls.begin(); }
  iterator end() { return decls.end(); }
  unsigned size() { return decls.size(); }
  bool empty() { return decls.empty(); }
  DeclarationList& getDeclarations() { return decls; }
  void appendPrelude(std::string s) { prelude += s; }
};

std::ostream& operator<<(std::ostream& os, const Expr& e);
std::ostream& operator<<(std::ostream& os, const Expr* e);

std::ostream& operator<<(std::ostream& os, Decl& e);
std::ostream& operator<<(std::ostream& os, Decl* e);

}

#endif // BOOGIEAST_H
