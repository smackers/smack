#ifndef BOOGIE_AST_H_
#define BOOGIE_AST_H_

#include <string>
#include <vector>

using namespace std;

namespace smack {
   
    class Expr {
    public:
        virtual void print(ostream &os) const = 0;
        static Expr * eq(Expr *l, Expr *r);
        static Expr * fn(string f, Expr *x);
        static Expr * fn(string f, Expr *x, Expr *y);
        static Expr * fn(string f, Expr *x, Expr *y, Expr *z);
        static Expr * id(string x);
        static Expr * lit(int i);
        static Expr * lit(int i, unsigned w);
        static Expr * lit(bool b);
        static Expr * neq(Expr *l, Expr *r);
        static Expr * not_(Expr *e);
        static Expr * sel(Expr *b, Expr *i);
        static Expr * sel(string b, string i);
    };
        
    class BinExpr : public Expr {
    public:
        enum Binary { Iff, Imp, Or, And, Eq, Neq, Lt, Gt, Lte, Gte, Sub, Conc,
                      Plus, Minus, Times, Div, Mod };
    private:
        Binary op;
        Expr *lhs;
        Expr *rhs;
    public:
        BinExpr(Binary b, Expr *l, Expr *r) : op(b), lhs(l), rhs(r) {}
        void print(ostream &os) const;
    };
    
    class FunExpr : public Expr {
        string fun;
        vector<Expr*> args;
    public:
        FunExpr(string f, vector<Expr*> xs) : fun(f), args(xs) {}
        void print(ostream &os) const;
    };
    
    class LitExpr : public Expr {
    public:
        enum Literal { True, False, Num, Bv8, Bv32, Bv64 };
    private:
        Literal lit;
        int val;
        int width;
    public:
        LitExpr(bool b) : lit(b ? True : False) {}
        LitExpr(int i) : lit(Num), val(i) {}
        LitExpr(Literal l, int i) : lit(l), val(i) {}
        void print(ostream &os) const;
    };
    
    class NegExpr : public Expr {
        Expr *expr;
    public:
        NegExpr(Expr *e) : expr(e) {}
        void print(ostream &os) const;
    };
    
    class NotExpr : public Expr {
        Expr *expr;
    public:
        NotExpr(Expr *e) : expr(e) {}
        void print(ostream &os) const;
    };
    
    class QuantExpr : public Expr {
    public:
        enum Quantifier { Forall, Exists };
    private:
        Quantifier q;
    public:
        void print(ostream &os) const;
    };
    
    class SelExpr : public Expr {
        Expr *base;
        vector<Expr*> idxs;
    public:
        SelExpr(Expr *a, vector<Expr*> i) : base(a), idxs(i) {}
        SelExpr(Expr *a, Expr* i) : base(a), idxs(vector<Expr*>(1,i)) {}
        void print(ostream &os) const;
    };    
    
    class UpdExpr : public Expr {
        Expr *base;
        vector<Expr*> idxs;
        Expr *val;
    public:
        UpdExpr(Expr *a, vector<Expr*> i, Expr *v) 
            : base(a), idxs(i), val(v) {}
        UpdExpr(Expr *a, Expr* i, Expr *v) 
            : base(a), idxs(vector<Expr*>(1,i)), val(v) {}
        void print(ostream &os) const;
    };
    
    class VarExpr : public Expr {
        const string var;
    public:
        VarExpr(const string v) : var(v) {}
        void print(ostream &os) const;
    };
    
    class Stmt {
    public:
        static Stmt * assert_(Expr *e);
        static Stmt * assign(Expr *e, Expr *f);
        static Stmt * assume(Expr *e);
        static Stmt * call(string p, Expr *x);
        static Stmt * call(string p, Expr *x, string r);
        static Stmt * call(string p, Expr *x, Expr *y, string r);
        static Stmt * call(string p, vector<Expr*> ps, vector<string> rs);
        static Stmt * goto_(string t);
        static Stmt * goto_(string t, string u);
        static Stmt * return_();
        virtual void print(ostream &os) const = 0;
    };
    
    class AssertStmt : public Stmt {
        Expr *expr;
    public:
        AssertStmt(Expr *e) : expr(e) {}
        void print(ostream &os) const;
    };
    
    class AssignStmt : public Stmt {
        vector<Expr*> lhs;
        vector<Expr*> rhs;
    public:
        AssignStmt(vector<Expr*> lhs, vector<Expr*> rhs) : lhs(lhs), rhs(rhs) {}
        void print(ostream &os) const;
    };
    
    class AssumeStmt : public Stmt {
        Expr *expr;
    public:
        AssumeStmt(Expr *e) : expr(e) {}
        void print(ostream &os) const;
    };   
    
    class CallStmt : public Stmt {
        string proc;
        vector<Expr*> params;
        vector<string> returns;
    public:
        CallStmt(string p, vector<Expr*> ps, vector<string> rs)
            : proc(p), params(ps), returns(rs) {}
        void print(ostream &os) const;
    };
    
    class GotoStmt : public Stmt {
        vector<string> targets;
    public:
        GotoStmt(vector<string> ts) : targets(ts) {}
        void print(ostream &os) const;
    };

    class HavocStmt : public Stmt {
        vector<string> vars;
    public:
        HavocStmt(vector<string> vs) : vars(vs) {}
        HavocStmt(string v) 
            : vars(vector<string>(1,v)) {}
        void print(ostream &os) const;
    };
    
    class ReturnStmt : public Stmt {
    public:
        ReturnStmt() {}
        void print(ostream &os) const;
    };    
    
    class Decl {
    protected:
        string name;
        string type;
        Decl(string n, string t) : name(n), type(t) {}
    public:
        virtual void print(ostream &os) const = 0;
        string getName() const { return name; }
        string getType() const { return type; }
    };

    class AxiomDecl : public Decl {
        Expr *expr;
    public:
        AxiomDecl(Expr *e) : Decl("",""), expr(e) {}
        void print(ostream &os) const;
    };
    
    class ConstDecl : public Decl {
        bool unique;
    public:
        ConstDecl(string n, string t, bool u) : Decl(n,t), unique(u) {}
        ConstDecl(string n, string t) : Decl(n,t), unique(false) {}
        void print(ostream &os) const;
    };    
    
    class FuncDecl : public Decl {
        vector< pair<string,string> > params;
        Expr *body;
    public:
        FuncDecl(string n, vector< pair<string,string> > ps, string t, Expr *b) 
            : Decl(n,""), params(ps), body(b) {}
        void print(ostream &os) const;
    };
    
    class VarDecl : public Decl {
    public:
        VarDecl(string n, string t) : Decl(n,t) {}
        void print(ostream &os) const;
    };
    
    class Block {
        string name;
        vector<Stmt*> stmts;
    public:
        Block() : name("") {}
        Block(string n) : name(n) {}
        void print(ostream &os) const;
        void addStmt(Stmt *s) { stmts.push_back(s); }
        string getName() { return name; }
    };
        
    class Procedure {
        string name;
        vector< pair<string,string> > params;
        vector< pair<string,string> > rets;
        vector<string> mods;
        vector<Decl*> decls;
        vector<Block*> blocks;
    public:
        Procedure(string n) : name(n) {}
        void print(ostream &os) const;
        void addParam(string x, string t) { params.push_back(make_pair(x,t)); }
        void addRet(string x, string t) { rets.push_back(make_pair(x,t)); }
        void addMod(string m) { mods.push_back(m); }
        void addDecl(Decl *d) { decls.push_back(d); }
        bool hasDecl(Decl *d) {
            for (unsigned i=0; i<decls.size(); i++)
                if (d->getName() == decls[i]->getName() 
                    && d->getType() == decls[i]->getType())
                    return true;
            return false;
        }
        void addBlock(Block *b) { blocks.push_back(b); }
    };
        
    class Program {
        vector<Decl*> decls;
        vector<Procedure*> procs;
    public:
        Program() { }
        void print(ostream &os) const;
        void addDecl(Decl *d) { decls.push_back(d); }
        void addProc(Procedure *p) { procs.push_back(p); }
    };    
}

#endif // BOOGIE_AST_H_
