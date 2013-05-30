#include "BoogieAst.h"
#include "llvm/Constants.h"
#include <sstream>

using namespace std;

namespace smack {

    Expr * Expr::eq(Expr *l, Expr *r) {
        return new BinExpr(BinExpr::Eq, l, r);
    }

    Expr * Expr::fn(string f, Expr *x) {
        return new FunExpr(f,vector<Expr*>(1,x));
    }    
    
    Expr * Expr::fn(string f, Expr *x, Expr *y) {
        vector<Expr*> ps(2,NULL);
        ps[0] = x;
        ps[1] = y;
        return new FunExpr(f,ps);
    }    

    Expr * Expr::fn(string f, Expr *x, Expr *y, Expr *z) {
        vector<Expr*> ps(3,NULL);
        ps[0] = x;
        ps[1] = y;
        ps[2] = z;
        return new FunExpr(f,ps);
    }
    
    Expr * Expr::id(string s) { return new VarExpr(s); }
    Expr * Expr::lit(int i) { return new LitExpr(i); }
    Expr * Expr::lit(int i, unsigned w) {
        switch (w) {
            case 0: return new LitExpr(i);
            case 8: return new LitExpr(LitExpr::Bv8, i);
            case 32: return new LitExpr(LitExpr::Bv32, i);
            case 64: return new LitExpr(LitExpr::Bv64, i);
            default: assert( false && "unexpected integer width." );
        }
    }
    
    Expr * Expr::lit(bool b) { return new LitExpr(b); }
    
    Expr * Expr::neq(Expr *l, Expr *r) {
        return new BinExpr(BinExpr::Neq, l, r);
    }
    
    Expr * Expr::not_(Expr *e) {
        return new NotExpr(e);
    }
    
    Expr * Expr::sel(Expr *b, Expr *i) {
        return new SelExpr(b,i);
    }
    
    Expr * Expr::sel(string b, string i) {
        return new SelExpr(id(b), id(i));
    }
    
    Stmt * Stmt::assert_(Expr *e) {
        return new AssertStmt(e);
    }
    
    Stmt * Stmt::assign(Expr *e, Expr *f) {
        return new AssignStmt(vector<Expr*>(1,e), vector<Expr*>(1,f));
    }
    
    Stmt * Stmt::assume(Expr *e) {
        return new AssumeStmt(e);
    }
    
    Stmt * Stmt::call(string p, Expr *x) {
        return call(p, vector<Expr*>(1,x), vector<string>());
    }
    
    Stmt * Stmt::call(string p, Expr *x, string r) {
        return call(p, vector<Expr*>(1,x), vector<string>(1,r));
    }
    
    Stmt * Stmt::call(string p, Expr *x, Expr *y, string r) {
        vector<Expr*> ps(2,NULL);
        ps[0] = x;
        ps[1] = y;
        return call(p, ps, vector<string>(1,r));
    }
    
    Stmt * Stmt::call(string p, vector<Expr*> ps, vector<string> rs) {
        return new CallStmt(p, ps, rs);
    }
    
    Stmt * Stmt::goto_(string t) {
        return new GotoStmt(vector<string>(1,t));
    }
    
    Stmt * Stmt::goto_(string t, string u) {
        vector<string> ts(2,"");
        ts[0] = t;
        ts[1] = u;
        return new GotoStmt(ts);
    }
    
    Stmt * Stmt::return_() {
        return new ReturnStmt();
    }
    
    ostream &operator<<(ostream &os, const Expr& e) {
        e.print(os);
        return os;
    }
    ostream &operator<<(ostream &os, const Expr *e) {
        e->print(os);
        return os;
    }
    ostream &operator<<(ostream &os, const Stmt *s) {
        s->print(os);
        return os;
    }
    ostream &operator<<(ostream &os, const Block *b) {
        b->print(os);
        return os;
    }    
    ostream &operator<<(ostream &os, const Decl *d) {
        d->print(os);
        return os;
    }
    ostream &operator<<(ostream &os, const Procedure *p) {
        p->print(os);
        return os;
    }
    ostream &operator<<(ostream &os, const Program *p) {
        if (p == 0) {
            os << "<null> Program!\n";
        } else {
            p->print(os);
        }
        return os;
    }
    ostream &operator<<(ostream &os, const Program& p) {
        p.print(os);
        return os;
    }
    
    template<class T> void print_seq(ostream &os, vector<T> ts,
        string init, string sep, string term) {          

        os << init;
        for (typename vector<T>::iterator i = ts.begin(); i != ts.end(); ++i)
            os << (i == ts.begin() ? "" : sep) << *i;
        os << term;
    }    
    template<class T> void print_seq(ostream &os, vector<T> ts, string sep) {
        print_seq<T>(os,ts,"",sep,"");
    }    
    template<class T> void print_seq(ostream &os, vector<T> ts) {
        print_seq<T>(os,ts,"","","");
    }
    
    void BinExpr::print(ostream &os) const { 
        os << "(" << lhs << " ";
        switch (op) {
            case Iff: os << "<==>"; break;
            case Imp: os << "==>"; break;
            case Or: os << "||"; break;
            case And: os << "&&"; break;
            case Eq: os << "=="; break;
            case Neq: os << "!="; break;
            case Lt: os << "<"; break;
            case Gt: os << ">"; break;
            case Lte: os << "<="; break;
            case Gte: os << ">="; break;
            case Sub: os << "<:"; break;
            case Conc: os << "++"; break;
            case Plus: os << "+"; break;
            case Minus: os << "-"; break;
            case Times: os << "*"; break;
            case Div: os << "/"; break;
            case Mod: os << "%"; break;
        }
        os << " " << rhs << ")";
    }
    
    void FunExpr::print(ostream &os) const {
        os << fun;
        print_seq<Expr*>(os,args,"(",", ",")");
    }

    void LitExpr::print(ostream &os) const {
        switch (lit) {
            case True: os << "true"; break;
            case False: os << "false"; break;
            case Num: os << val; break;
            case Bv8: os << val << "bv8"; break;
            case Bv32: os << val << "bv32"; break;
            case Bv64: os << val << "bv64"; break;
        }
    }

    void NegExpr::print(ostream &os) const {
        os << "-(" << expr << ")";
    }

    void NotExpr::print(ostream &os) const {
        os << "!(" << expr << ")";
    }

    void QuantExpr::print(ostream &os) const {
        os << "(";
        switch (q) {
            case Forall: os << "forall"; break;
            case Exists: os << "exists"; break;
        }
        os << " -- ToDo: Implement quantified expressions. ";
        os << ")";
    }

    void SelExpr::print(ostream &os) const { 
        os << base;
        print_seq<Expr*>(os,idxs,"[",", ","]");
    }

    void UpdExpr::print(ostream &os) const { 
        os << base << "[";
        print_seq<Expr*>(os,idxs,", ");
        os << " := " << val << "]";
    }

    void VarExpr::print(ostream &os) const { 
        os << var;
    }
    
    void AssertStmt::print(ostream &os) const {
        os << "assert " << expr;
    }

    void AssignStmt::print(ostream &os) const {            
        print_seq<Expr*>(os,lhs,", ");
        os << " := ";            
        print_seq<Expr*>(os,rhs,", ");
    }

    void AssumeStmt::print(ostream &os) const {
        os << "assume " << expr;
    }

    void CallStmt::print(ostream &os) const {
        os << "call ";
        if (returns.size() > 0)
            print_seq<string>(os,returns,"",", "," := ");
        os << proc;
        print_seq<Expr*>(os,params,"(",", ",")");
    }
    
    void GotoStmt::print(ostream &os) const {
        os << "goto ";
        print_seq<string>(os,targets,", ");
    }
    
    void HavocStmt::print(ostream &os) const {
        os << "havoc ";
        print_seq<string>(os,vars,", ");
    }

    void ReturnStmt::print(ostream &os) const {
        os << "return";
    }
    
    void AxiomDecl::print(ostream &os) const {
        os << "axiom " << expr << ";";
    }

    void ConstDecl::print(ostream &os) const {
        os << "const " << (unique ? "unique " : "") 
            << name << ": " << type << ";";
    }
    
    void FuncDecl::print(ostream &os) const {
        os << "function " << name;
        for (unsigned i=0; i < params.size(); i++)
            os << params[i].first << ": " << params[i].second
                << (i < params.size()-1 ? ", " : "");
        os << ": " << type << " { " << body << " };";
    }
    
    void VarDecl::print(ostream &os) const {
        os << "var " << name << ": " << type << ";";
    }

    void Block::print(ostream &os) const {
        if (name != "")
            os << name << ":" << endl;
        print_seq<Stmt*>(os,stmts,"  ",";\n  ",";");
    }

    void Procedure::print(ostream &os) const {
        os << "procedure " << name << "(";
        for (unsigned i=0; i < params.size(); i++)
            os << params[i].first << ": " << params[i].second
                << (i < params.size()-1 ? ", " : "");
        os << ") ";
        if (rets.size() > 0) {
            os << endl;
            os << "  returns (";
            for (unsigned i=0; i < rets.size(); i++)
                os << rets[i].first << ": " << rets[i].second
                    << (i < rets.size()-1 ? ", " : "");
            os << ") ";
        }
        if (mods.size() > 0) {
            os << endl;
            print_seq<string>(os,mods, "  modifies ", ", ", ";");
            os << endl;
        }
        os << "{" << endl;
        print_seq<Decl*>(os,decls,"  ","\n  ","\n");
        print_seq<Block*>(os,blocks,"\n");
        os << endl << "}" << endl;
    }

    void Program::print(ostream &os) const {
        os << "// BEGIN SMACK-GENERATED CODE" << endl;
        print_seq<Decl*>(os,decls,"\n");
        os << endl;
        print_seq<Procedure*>(os,procs,"\n");
        os << "// END SMACK-GENERATED CODE" << endl;
    }
}
