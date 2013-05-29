//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "SmackGenerator.h"
#include <sstream>

using namespace smack;
using namespace std;

RegisterPass<SmackGenerator> X("smack", "SMACK generator pass");
char SmackGenerator::ID = 0;

string blockName(int n) {
    ostringstream s;
    s << "$bb" << n;
    return s.str();
}

bool SmackGenerator::runOnModule(llvm::Module &m) {

    program = new Program();

    DEBUG(errs() << "Analyzing globals...\n");

    vector<string> globals;
    
    for (llvm::Module::const_global_iterator 
        x = m.global_begin(), e = m.global_end(); x != e; ++x) {
            
        if (isa<GlobalVariable>(x)) {
            string name = translateName(x); // TODO clean
            globals.push_back(name);
            program->addDecl(new ConstDecl(name, "$ptr", true));  
        }
    }
    
    // AXIOMS about variable uniqueness
    for (unsigned i=0; i<globals.size(); i++)
        for (unsigned j=i+1; j<globals.size(); j++)
            program->addDecl(new AxiomDecl(
                Expr::neq( Expr::id(globals[i]), 
                    Expr::id(globals[j]))
            ));

    DEBUG(errs() << "Analyzing functions...\n");

    for (llvm::Module::iterator func = m.begin(), e = m.end(); func != e; ++func) {

        string name = func->getName().str();
        
        // TODO clean
        if (func->isDeclaration() || name.find("__SMACK") != string::npos ) {
            continue;
        }
        
        DEBUG(errs() << "Analyzing function: " << name << "\n");

        Procedure *proc = new Procedure(name);

        // POINTER TO THIS FUNCTION
        program->addDecl(new ConstDecl(name + "#ptr", "$ptr", true));
        program->addProc(proc);
            
        // PARAMETERS
        for (llvm::Function::const_arg_iterator
                arg = func->arg_begin(), e = func->arg_end(); arg != e; ++arg) {
            proc->addParam(
                translateName(arg),  // TODO clean
                arg->getType()->isIntegerTy(1) ? "bool" : "$ptr" );
        }
        
        // RETURNS
        if (func->getReturnType()->isVoidTy()) ;
        else if (func->getReturnType()->isIntegerTy(1)) proc->addRet("$r","bool");
        else proc->addRet("$r","$ptr");
        
        // MODIFIES
        proc->addMod("$Mem");
        proc->addMod("$Alloc");

        // BODY
        if ( !func->isDeclaration() && !func->empty() 
            && !func->getEntryBlock().empty() ) {    

            map<const llvm::BasicBlock*, Block*> known;
            stack<llvm::BasicBlock*> workStack;    
            int bn = 0;

            llvm::BasicBlock& entryBlock = func->getEntryBlock();
            workStack.push(&entryBlock);

            Block *entry = new Block(blockName(bn++));
            proc->addBlock(entry);
            known[&entryBlock] = entry;
            SmackInstVisitor visitor(&getAnalysis<DataLayout>(), proc, entry);

            // INVARIANT: knownBlocks.CONTAINS(b) iff workStack.CONTAINS(b) or  
            // workStack.CONTAINED(b) at some point in time.
            while (!workStack.empty()) {      
                llvm::BasicBlock *llvmBlock = workStack.top(); workStack.pop();
                Block *block = known[llvmBlock];

                visitor.setCurrBlock(block);
                visitor.visit(llvmBlock);

                for (succ_iterator i = succ_begin(llvmBlock),
                        e = succ_end(llvmBlock); i != e; ++i) {

                    llvm::BasicBlock* llvmSucc = *i;
                    Block *succ;
          
                    if (known.count(llvmSucc) == 0) {
                        succ = new Block(blockName(bn++));
                        proc->addBlock(succ);
                        known[llvmSucc] = succ;
                        workStack.push(llvmSucc);
                    } else {
                        succ = known[llvmSucc];
                    }
                    
                    // create a successor link
                    block->addSucc(succ);
                    for (llvm::BasicBlock::iterator
                        s = llvmSucc->begin(), e = llvmSucc->end(); s != e && isa<PHINode>(s); ++s) {
                            
                        // write to the phi-node variable of the successor
                        PHINode* phi = cast<PHINode>(s);
                        if (Value* v = phi->getIncomingValueForBlock(llvmBlock)) 
                            block->addStmt(Stmt::assign(visitor.expr(phi),visitor.expr(v)));
                    }
                }
            }
        }

        DEBUG(errs() << "Finished analyzing function: " << name << "\n\n");
    }
    return false;
}
