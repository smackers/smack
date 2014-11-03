//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/Slicing.h"
#include "smack/SmackInstGenerator.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Debug.h"
#include <vector>
#include <queue>
#include <set>

using namespace std;
using namespace llvm;

namespace smack {

typedef SmallVector< pair<const BasicBlock*, const BasicBlock*>, 10 > EdgeList;

bool contains(EdgeList& backedges, const BasicBlock* src, const BasicBlock* tgt) {
  for (EdgeList::iterator E = backedges.begin(), End = backedges.end(); E != End; ++E) {
    if (E->first == src && E->second == tgt)
      return true;
  }
  return false;
}

bool hasIncomingBackEdge(PHINode* Phi, EdgeList& backedges) {
  for (PHINode::block_iterator B = Phi->block_begin(); B != Phi->block_end(); ++B) {
    if (contains(backedges,*B,Phi->getParent()))
      return true;
  }
  return false;
}

Value* getQuantifiedVariable(Instruction* I) {
  if (CallInst* CI = dyn_cast<CallInst>(I))
    if (Function* F = CI->getCalledFunction())
      if (F->hasName() && F->getName().find("qvar") != string::npos)
        if (ConstantExpr* CE = dyn_cast<ConstantExpr>(CI->getArgOperand(0)))
          if (CE->getOpcode() == Instruction::GetElementPtr)
            if (GlobalValue* G = dyn_cast<GlobalValue>(CE->getOperand(0)))
              if (ConstantDataSequential* S = dyn_cast<ConstantDataSequential>(G->getOperand(0)))
                return S;
  return 0;
}

GlobalValue* usedGlobal(User* U) {
  GlobalValue* G = 0;
  for (User::op_iterator V = U->op_begin(), E = U->op_end(); V != E; ++V) {
    if (dyn_cast<Instruction>(V))
      continue;
    if ((G = dyn_cast<GlobalValue>(V)))
      break;
    if ((U = dyn_cast<User>(V)) && (G = usedGlobal(U)))
      break;
  }
  return G;
}

Slice* getSubslice(Instruction* I, Slices& slices) {
  if (CallInst* CI = dyn_cast<CallInst>(I))
    if (Function* F = CI->getCalledFunction())
      if (F->hasName())
        if (F->getName().find("forall") != string::npos ||
            F->getName().find("exists") != string::npos)
          if (ConstantInt* C = dyn_cast<ConstantInt>(CI->getArgOperand(1))) {
            uint64_t i = C->getLimitedValue();
            assert(slices.size() > i && "Did not find expression.");
            return slices[i];
          }

  return 0;
}

pair<string,string> getParameter(Value* V, Naming& naming, SmackRep& rep) {
  
  if (GlobalVariable* G = dyn_cast<GlobalVariable>(V)) {
    unsigned r = rep.getRegion(G);
    return make_pair(rep.memReg(r), rep.memType(r));
  }

  else if (ConstantDataSequential* S = dyn_cast<ConstantDataSequential>(V))
    return make_pair(S->getAsCString(), "int");

  else if (V->hasName() && V->getName().find("result") != string::npos)
    return make_pair(Naming::RET_VAR, rep.type(V));

  else
    return make_pair(naming.get(*V), rep.type(V));
}

Slice::Slice(Instruction& I, Slices& S, string name)
  : value(I), block(*I.getParent()), function(*block.getParent()),
    context(function.getContext()), slices(S), name(name) {

  EdgeList backedges;
  FindFunctionBackedges(function, backedges);

  queue<Instruction*> workList;
  workList.push(&I);

  while (!workList.empty()) {
    Instruction* I = workList.front();
    workList.pop();
    if (values.count(I) || inputs.count(I))
      continue;

    if (PHINode* Phi = dyn_cast<PHINode>(I)) {
      if (hasIncomingBackEdge(Phi, backedges)) {
        inputs.insert(I);
        continue;
      }
    }

    if (GlobalValue* G = usedGlobal(I))
      inputs.insert(G);

    if (Value* Q = getQuantifiedVariable(I))
      inputs.insert(Q);

    // Add inputs from any subslices, excluding quantified variables
    if (Slice* S = getSubslice(I,slices))
      for (unordered_set<Value*>::iterator V = S->inputs.begin(),
          E = S->inputs.end(); V != E; ++V)
        if (!inputs.count(*V) && !dyn_cast<ConstantDataSequential>(*V))
          inputs.insert(*V);

    values.insert(I);
    values.insert(I->getParent());

    // ENSURE EACH BLOCK HAS A TERMINATOR
    if (BranchInst* Br = dyn_cast<BranchInst>(I->getParent()->getTerminator()))
      if (I->getParent() != &block)
        workList.push(Br);

    if (BranchInst* Br = dyn_cast<BranchInst>(I)) {
      if (Br->isConditional()) {
        if (Instruction* J = dyn_cast<Instruction>(Br->getCondition())) {
          workList.push(J);
        }
        values.insert(Br->getSuccessor(1));
      }
      values.insert(Br->getSuccessor(0));
      continue;
    }

    if (PHINode* Phi = dyn_cast<PHINode>(I)) {
      for (PHINode::block_iterator B = Phi->block_begin(); B != Phi->block_end(); ++B) {
        workList.push( (*B)->getTerminator() );
      }
    }

    for (User::op_iterator U = I->op_begin(); U != I->op_end(); ++U) {
      if (Instruction* J = dyn_cast<Instruction>(U)) {
        if (!contains(backedges,J->getParent(),I->getParent())) {
          workList.push(J);
        }
      }
    }
  }

}

void Slice::remove() {
  // Instruction* I = dyn_cast<Instruction>(&value);
  // assert(I && "Expected instruction value.");

  // map<BasicBlock*,BasicBlock*> succ;

  queue<Value*> workList;
  set<Value*> deleted;
  workList.push(&value);

  while (!workList.empty()) {
    Value* V = workList.front();
    workList.pop();

    if (deleted.count(V))
      continue;

    if (V->getNumUses() > 0)
      continue;

    if (User* U = dyn_cast<User>(V))
      for (User::op_iterator W = U->op_begin(); W != U->op_end(); ++W)
        workList.push(*W);

    if (PHINode* I = dyn_cast<PHINode>(V))
      for (PHINode::block_iterator A = I->block_begin(), Z = I->block_end();
          A != Z; ++ A)
        workList.push((*A)->getTerminator());

    if (BranchInst* I = dyn_cast<BranchInst>(V)) {
      if (I->isConditional()) {
        Value* C = I->getCondition();
        workList.push(C);
        I->setCondition(UndefValue::get(C->getType()));
      }
      continue;
    }

    if (Instruction* I = dyn_cast<Instruction>(V))
      I->eraseFromParent();

    deleted.insert(V);
  }
}

string Slice::getName() {
  return name;
}

const Expr* Slice::getCode(Naming& naming, SmackRep& rep) {
  CodeExpr* code = new CodeExpr(rep.getProgram());
  SmackInstGenerator igen(rep, *code, naming, slices);

  for (Function::iterator B = function.begin(), E = function.end(); B != E; ++B) {
    if (!values.count(B))
      continue;
    igen.visitBasicBlock(*B);

    for (BasicBlock::iterator I = B->begin(), G = B->end(); I != G; ++I) {
      if (!values.count(&*I))
        continue;
      igen.visit(*I);
    }

    if (B == block) {
      igen.emit(Stmt::return_(rep.expr(&value)));

    } else if (!values.count(B->getTerminator())) {
      igen.emit(Stmt::assume(Expr::lit(false)));
      igen.emit(Stmt::return_(Expr::lit(true)));
    }
  }
  return code;
}

const Decl* Slice::getBoogieDecl(Naming& naming, SmackRep& rep) {
  if (name == "")
    return 0;
  naming.enter();
  vector< pair<string,string> > params;
  for (unordered_set<Value*>::iterator V = inputs.begin(), E = inputs.end(); V != E; ++V)
    params.push_back(getParameter(*V,naming,rep));
  Decl* D = Decl::function(getName(),params,"bool",getCode(naming,rep));
  D->addAttr(Attr::attr("inline"));
  naming.leave();
  return D;
}

const Expr* Slice::getBoogieExpression(Naming& naming, SmackRep& rep) {
  if (name == "") {
    naming.enter();
    const Expr* code = getCode(naming,rep);
    naming.leave();
    return code;
  }

  vector<const Expr*> args;
  for (unordered_set<Value*>::iterator V = inputs.begin(), E = inputs.end(); V != E; ++V)
    args.push_back(Expr::id(getParameter(*V,naming,rep).first));
  return Expr::fn(getName(),args);
}

}
