//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/SmackInstGenerator.h"
#include "smack/SmackOptions.h"
#include "llvm/DebugInfo.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/InstVisitor.h"
#include <sstream>

namespace smack {

using llvm::errs;
using namespace std;
  
const bool CODE_WARN = true;
const bool SHOW_ORIG = false;

#define WARN(str) \
    if (CODE_WARN) currBlock->addStmt(Stmt::comment(string("WARNING: ") + str))
#define ORIG(ins) \
    if (SHOW_ORIG) currBlock->addStmt(Stmt::comment(i2s(ins)))

string i2s(llvm::Instruction& i) {
  string s;
  llvm::raw_string_ostream ss(s);
  ss << i;
  s = s.substr(2);
  return s;
}

Block* SmackInstGenerator::createBlock() {
  stringstream s;
  s << SmackRep::BLOCK_LBL << blockNum++;
  Block* b = new Block(s.str());
  currProc.addBlock(b);
  return b;
}

string SmackInstGenerator::createVar() {
  stringstream s;
  s << "$x" << varNum++;
  string name = s.str();
  currProc.addDecl(new VarDecl(name, rep->getPtrType()));
  return name;
}

void SmackInstGenerator::nameInstruction(llvm::Instruction& inst) {
  if (!inst.getType()->isVoidTy()) {
    if (!inst.hasName())
      inst.setName(rep->isBool(&inst) ? SmackRep::BOOL_VAR : SmackRep::PTR_VAR);
    VarDecl* d = new VarDecl(rep->id(&inst), rep->type(&inst));
    if (!currProc.hasDecl(d))
      currProc.addDecl(d);
  }
}

void SmackInstGenerator::annotate(llvm::Instruction& i, Block* b) {

  if (llvm::MDNode* n = i.getMetadata("dbg")) {      
    llvm::DILocation l(n);
    
    if (SmackOptions::SourceLocSymbols)
      b->addStmt(Stmt::annot(
                 Attr::attr("sourceloc",
                            l.getFilename().str(),
                            l.getLineNumber(),
                            l.getColumnNumber())));
  }
}

void SmackInstGenerator::processInstruction(llvm::Instruction& inst) {
  DEBUG(errs() << "Inst: " << inst << "\n");
  DEBUG(errs() << "Inst name: " << inst.getName().str() << "\n");
  annotate(inst, currBlock);
  ORIG(inst);
  nameInstruction(inst);
}

void SmackInstGenerator::visitInstruction(llvm::Instruction& inst) {
  DEBUG(errs() << "Instruction not handled: " << inst << "\n");
  assert(false && "Instruction not handled");
}

void SmackInstGenerator::visitAllocaInst(llvm::AllocaInst& ai) {
  processInstruction(ai);
  unsigned typeSize = rep->storageSize(ai.getAllocatedType());
  llvm::Value* arraySize = ai.getArraySize();
  currBlock->addStmt(Stmt::call(
                       SmackRep::ALLOCA,
                       Expr::fn(SmackRep::MUL, rep->lit(typeSize), rep->lit(arraySize)),
                       rep->id(&ai)));
}

void SmackInstGenerator::generatePhiAssigns(llvm::TerminatorInst& ti) {
  llvm::BasicBlock* block = ti.getParent();
  for (unsigned i = 0; i < ti.getNumSuccessors(); i++) {

    // write to the phi-node variable of the successor
    for (llvm::BasicBlock::iterator
         s = ti.getSuccessor(i)->begin(), e = ti.getSuccessor(i)->end();
         s != e && llvm::isa<llvm::PHINode>(s); ++s) {

      llvm::PHINode* phi = llvm::cast<llvm::PHINode>(s);
      if (llvm::Value* v =
            phi->getIncomingValueForBlock(block)) {

        nameInstruction(*phi);
        currBlock->addStmt(Stmt::assign(
                             rep->expr(phi), rep->expr(v)));
      }
    }
  }
}

void SmackInstGenerator::generateGotoStmts(
  llvm::Instruction& inst,
  vector<pair<const Expr*, string> > targets) {

  assert(targets.size() > 0);

  if (targets.size() > 1) {
    vector<string> dispatch;

    for (unsigned i = 0; i < targets.size(); i++) {
      Block* b = createBlock();
      annotate(inst, b);
      b->addStmt(Stmt::assume(targets[i].first));
      b->addStmt(Stmt::goto_(targets[i].second));
      dispatch.push_back(b->getName());
    }

    currBlock->addStmt(Stmt::goto_(dispatch));

  } else
    currBlock->addStmt(Stmt::goto_(targets[0].second));
}

void SmackInstGenerator::visitBranchInst(llvm::BranchInst& bi) {
  processInstruction(bi);

  // Collect the list of tarets
  vector<pair<const Expr*, string> > targets;

  if (bi.getNumSuccessors() == 1) {

    // Unconditional branch
    assert(blockMap.count(bi.getSuccessor(0)) != 0);
    targets.push_back(make_pair(Expr::lit(true),
                                blockMap[bi.getSuccessor(0)]->getName()));

  } else {

    // Conditional branch
    assert(bi.getNumSuccessors() == 2);
    assert(blockMap.count(bi.getSuccessor(0)) != 0);
    assert(blockMap.count(bi.getSuccessor(1)) != 0);

    const Expr* e = rep->expr(bi.getCondition());
    targets.push_back(make_pair(e,
                                blockMap[bi.getSuccessor(0)]->getName()));
    targets.push_back(make_pair(Expr::not_(e),
                                blockMap[bi.getSuccessor(1)]->getName()));
  }
  generatePhiAssigns(bi);
  generateGotoStmts(bi, targets);
}

void SmackInstGenerator::visitSwitchInst(llvm::SwitchInst& si) {
  processInstruction(si);

  // Collect the list of tarets
  vector<pair<const Expr*, string> > targets;

  const Expr* e = rep->expr(si.getCondition());
  const Expr* n = Expr::lit(true);

  for (llvm::SwitchInst::CaseIt
       i = si.case_begin(); i != si.case_begin(); ++i) {

    assert(blockMap.count(i.getCaseSuccessor()) != 0);
    const Expr* v = rep->expr(i.getCaseValue());
    targets.push_back(make_pair(Expr::eq(e, v),
                                blockMap[i.getCaseSuccessor()]->getName()));

    // Add the negation of this case to the default case
    n = Expr::and_(n, Expr::neq(e, v));
  }

  // The default case
  assert(blockMap.count(si.getDefaultDest()) != 0);
  targets.push_back(make_pair(n,
                              blockMap[si.getDefaultDest()]->getName()));

  generatePhiAssigns(si);
  generateGotoStmts(si, targets);
}

void SmackInstGenerator::visitPHINode(llvm::PHINode& phi) {
  // NOTE: this is really a No-Op, since assignments to the phi nodes
  // are handled in the translation of branch/switch instructions.
  processInstruction(phi);
}

void SmackInstGenerator::visitTruncInst(llvm::TruncInst& ti) {
  processInstruction(ti);
  WARN("ignoring trunc instruction : " + i2s(ti));
  currBlock->addStmt(Stmt::assign(
                       rep->expr(&ti), rep->expr(ti.getOperand(0))));
}

void SmackInstGenerator::visitUnreachableInst(llvm::UnreachableInst& ii) {
  processInstruction(ii);
}

// TODO Should we put this DEBUG info back in ?
// void SmackInstGenerator::processIndirectCall(CallInst& ci) {
// DEBUG(errs() << "Called value: " << *calledValue << "\n");
// DEBUG(errs() << "Called value type: " << *calledValueType << "\n");
// DEBUG(errs() << "Called function type: " << *calledFuncType << "\n");


// TODO When will we revive the DSA code ?
// #ifdef USE_DSA
//     CallSite callSite = CallSite::get(&ci);
//     if (ci.getCalledFunction() != NULL) {
//       Function* calledFunction = ci.getCalledFunction();
//       module->addCalledProcedure(calledFunction->getNameStr());
//       CalledFunction* calledFunc = stmt->addCalledFunction(calledFunction);
//
//       if ((Common::memoryType == DSA_INDEXED || Common::memoryType == DSA_SPLIT) &&
//           tdDataStructures->hasDSGraph(*calledFunction)) {
//         generateMemoryPairings(callSite, calledFunction, calledFunc);
//       }
//     } else {
//       for (vector<const Function*>::iterator i = callTargetFinder->begin(callSite),
//           ei = callTargetFinder->end(callSite); i != ei; ++i) {
//         const Function* calledFunction = *i;
//         module->addCalledProcedure(calledFunction->getNameStr());
//         if (ci.getCalledValue()->getType() == calledFunction->getType()) {
//           CalledFunction* calledFunc = stmt->addCalledFunction(calledFunction);
//
//           if ((Common::memoryType == DSA_INDEXED || Common::memoryType == DSA_SPLIT) &&
//               tdDataStructures->hasDSGraph(*calledFunction)) {
//             generateMemoryPairings(callSite, calledFunction, calledFunc);
//           }
//         }
//       }
//     }
// #endif
// }

// TODO Does this function belong here, or in "SmackRep" ?
const Stmt* SmackInstGenerator::generateCall(
  llvm::Function* f, vector<const Expr*> args, vector<string> rets) {

  string name = rep->id(f);

  if (rep->isSmackAssert(f)) {
    assert(args.size() == 1 && rets.size() == 0);
    return Stmt::assert_(
             Expr::neq(args[0], SmackRep::ZERO));

  } else if (rep->isSmackAssume(f)) {
    assert(args.size() == 1 && rets.size() == 0);
    return Stmt::assume(
             Expr::neq(args[0], SmackRep::ZERO));

  } else if (rep->isSmackRecInt(f)) {
    assert(args.size() == 1 && rets.size() == 0);
    return Stmt::call(SmackRep::BOOGIE_REC_INT, rep->off(args[0]));
//
//        } else if (rep->isSmackRecObj(f)) {
//            assert (args.size() == 1 && rets.size() == 0);
//            return Stmt::call(SmackRep::BOOGIE_REC_OBJ, rep->obj(args[0]));
//
//        } else if (rep->isSmackRecPtr(f)) {
//            assert (args.size() == 1 && rets.size() == 0);
//            return Stmt::call(SmackRep::BOOGIE_REC_PTR, args[0]);

  } else if (name == "malloc") {
    assert(args.size() == 1);
    return Stmt::call(SmackRep::MALLOC, rep->off(args[0]), rets[0]);

  } else if (name == "free") {
    assert(args.size() == 1);
    return Stmt::call(SmackRep::FREE, args[0]);

  } else if (f->isVarArg() && args.size() > 0) {

    // Handle variable argument functions
    missingDecls.insert(make_pair(f, args.size()));
    stringstream ss;
    ss << name << "#" << args.size();
    return Stmt::call(ss.str(), args, rets);

  } else if (f->isDeclaration() && !rep->isSmackName(name)) {

    // Handle functions without bodies (just declarations)
    missingDecls.insert(make_pair(f, args.size()));
    return Stmt::call(name, args, rets);

  } else {
    return Stmt::call(name, args, rets);
  }
}

void SmackInstGenerator::visitCallInst(llvm::CallInst& ci) {
  processInstruction(ci);

  if (ci.isInlineAsm()) {
    WARN("unsoundly ignoring inline asm call.");
    currBlock->addStmt(Stmt::skip());
    return;

  } else if (llvm::Function* f = ci.getCalledFunction()) {
    if (rep->id(f).find("llvm.dbg.") != string::npos) {
      // a "skip" statement..
      WARN("ignoring llvm.debug call.");
      currBlock->addStmt(Stmt::skip());
      return;
    }
  }

  vector<const Expr*> args;
  for (unsigned i = 0; i < ci.getNumOperands() - 1; i++)
    args.push_back(rep->expr(ci.getOperand(i)));

  vector<string> rets;
  if (!ci.getType()->isVoidTy())
    rets.push_back(rep->id(&ci));

  if (llvm::Function* f = ci.getCalledFunction()) {
    currBlock->addStmt(generateCall(f, args, rets));

  } else {
    // function pointer call...
    vector<llvm::Function*> fs;

    llvm::Value* c = ci.getCalledValue();
    DEBUG(errs() << "Called value: " << *c << "\n");

    // special case that happens when some clang warnings are reported
    // we can find out the called function exactly
    if (llvm::ConstantExpr* ce = llvm::dyn_cast<llvm::ConstantExpr>(c)) {
      if (ce->isCast()) {
        llvm::Value* castValue = ce->getOperand(0);
        if (llvm::Function* castFunc = llvm::dyn_cast<llvm::Function>(castValue)) {
          currBlock->addStmt(generateCall(castFunc, args, rets));
          return;
        }
      }
    }

    // Collect the list of possible function calls
    llvm::Type* t = c->getType();
    DEBUG(errs() << "Called value type: " << *t << "\n");
    assert(t->isPointerTy() && "Indirect call value type must be pointer");
    t = t->getPointerElementType();
    DEBUG(errs() << "Called function type: " << *t << "\n");

    llvm::Module* m = ci.getParent()->getParent()->getParent();
    for (llvm::Module::iterator f = m->begin(), e = m->end(); f != e; ++f)
      if (f->getFunctionType() == t)
        fs.push_back(f);

    if (fs.size() == 1) {
      // Q: is this case really possible?
      currBlock->addStmt(generateCall(fs[0], args, rets));

    } else if (fs.size() > 1) {
      Block* tail = createBlock();
      vector<string> targets;

      // Create a sequence of dispatch blocks, one for each call.
      for (unsigned i = 0; i < fs.size(); i++) {
        Block* disp = createBlock();
        targets.push_back(disp->getName());

        disp->addStmt(Stmt::assume(
                        Expr::eq(rep->expr(c), rep->expr(fs[i]))));
        disp->addStmt(generateCall(fs[i], args, rets));
        disp->addStmt(Stmt::goto_(tail->getName()));
      }

      // Jump to the dispatch blocks.
      currBlock->addStmt(Stmt::goto_(targets));

      // Update the current block for subsequent visits.
      currBlock = tail;

    } else {
      // In the worst case, we have no idea what function may have
      // been called...
      WARN("unsoundly ignoring indeterminate call.");
      currBlock->addStmt(Stmt::skip());
    }
  }
}

void SmackInstGenerator::visitReturnInst(llvm::ReturnInst& ri) {
  processInstruction(ri);

  if (llvm::Value* v = ri.getReturnValue())
    currBlock->addStmt(Stmt::assign(
                         Expr::id(SmackRep::RET_VAR), rep->expr(v)));

  currBlock->addStmt(Stmt::return_());
}

void SmackInstGenerator::visitLoadInst(llvm::LoadInst& li) {
  processInstruction(li);
  currBlock->addStmt(Stmt::assign(
                       rep->expr(&li),
                       rep->mem(li.getPointerOperand())));

  if (SmackOptions::MemoryModelDebug) {
    currBlock->addStmt(Stmt::call(SmackRep::REC_MEM_OP, Expr::id(SmackRep::MEM_READ)));
    currBlock->addStmt(Stmt::call(SmackRep::BOOGIE_REC_INT, rep->expr(li.getPointerOperand())));
    currBlock->addStmt(Stmt::call(SmackRep::BOOGIE_REC_INT, rep->expr(&li)));
  }
}

void SmackInstGenerator::visitStoreInst(llvm::StoreInst& si) {
  processInstruction(si);
  currBlock->addStmt(Stmt::assign(
                       rep->mem(si.getPointerOperand()),
                       rep->expr(si.getOperand(0))));
                       
  if (SmackOptions::MemoryModelDebug) {
    currBlock->addStmt(Stmt::call(SmackRep::REC_MEM_OP, Expr::id(SmackRep::MEM_WRITE)));
    currBlock->addStmt(Stmt::call(SmackRep::BOOGIE_REC_INT, rep->expr(si.getPointerOperand())));
    currBlock->addStmt(Stmt::call(SmackRep::BOOGIE_REC_INT, rep->expr(si.getOperand(0))));
  }
}

void SmackInstGenerator::visitGetElementPtrInst(llvm::GetElementPtrInst& gepi) {
  processInstruction(gepi);

  vector<llvm::Value*> ps;
  vector<llvm::Type*> ts;
  llvm::gep_type_iterator typeI = gep_type_begin(gepi);
  for (unsigned i = 1; i < gepi.getNumOperands(); i++, ++typeI) {
    ps.push_back(gepi.getOperand(i));
    ts.push_back(*typeI);
  }
  currBlock->addStmt(Stmt::assign(rep->expr(&gepi),
                                  rep->ptrArith(gepi.getPointerOperand(), ps, ts)));
}

void SmackInstGenerator::visitICmpInst(llvm::ICmpInst& ci) {
  processInstruction(ci);
  currBlock->addStmt(Stmt::assign(rep->expr(&ci), rep->pred(ci)));
}

void SmackInstGenerator::visitZExtInst(llvm::ZExtInst& ci) {
  processInstruction(ci);

  const Expr* e = rep->expr(ci.getOperand(0));
  if (rep->isBool(ci.getSrcTy())) e = rep->b2p(e);
  currBlock->addStmt(Stmt::assign(rep->expr(&ci), e));
}

void SmackInstGenerator::visitSExtInst(llvm::SExtInst& ci) {
  processInstruction(ci);

  const Expr* e = rep->expr(ci.getOperand(0));
  if (rep->isBool(ci.getSrcTy())) e = rep->b2p(e);
  currBlock->addStmt(Stmt::assign(rep->expr(&ci), e));
}

void SmackInstGenerator::visitBitCastInst(llvm::BitCastInst& ci) {
  processInstruction(ci);
  WARN("ignoring bitcast instruction : " + i2s(ci));
  currBlock->addStmt(Stmt::assign(
                       rep->expr(&ci), rep->expr(ci.getOperand(0))));
}

void SmackInstGenerator::visitBinaryOperator(llvm::BinaryOperator& bo) {
  processInstruction(bo);
  currBlock->addStmt(Stmt::assign(rep->expr(&bo), rep->op(bo)));
}

void SmackInstGenerator::visitAtomicCmpXchgInst(llvm::AtomicCmpXchgInst& i) {
  processInstruction(i);

  string x = createVar();

  const Expr
  *res = rep->expr(&i),
   *piv = rep->mem(i.getOperand(0)),
    *cmp = rep->expr(i.getOperand(1)),
     *swp = rep->expr(i.getOperand(2));

  // NOTE: could also do this with gotos, but perhaps we do not want to
  // spread atomic instructions across blocks (?)
  currBlock->addStmt(Stmt::assign(res, piv));
  currBlock->addStmt(Stmt::havoc(x));
  currBlock->addStmt(Stmt::assume(
                       Expr::impl(Expr::eq(piv, cmp), Expr::eq(Expr::id(x), swp))));
  currBlock->addStmt(Stmt::assume(
                       Expr::impl(Expr::neq(piv, cmp), Expr::eq(Expr::id(x), res))));
  currBlock->addStmt(Stmt::assign(piv, Expr::id(x)));
}

void SmackInstGenerator::visitPtrToIntInst(llvm::PtrToIntInst& i) {
  processInstruction(i);

  // TODO review this use of p2i
  currBlock->addStmt(Stmt::assign(rep->expr(&i),
                                  rep->p2i(rep->expr(i.getOperand(0)))));
}

void SmackInstGenerator::visitIntToPtrInst(llvm::IntToPtrInst& i) {
  processInstruction(i);
  WARN("possible loss of precision : " + i2s(i));

  // TODO review this use of i2p
  currBlock->addStmt(Stmt::assign(rep->expr(&i),
                                  rep->i2p(rep->expr(i.getOperand(0)))));
}

void SmackInstGenerator::visitSelectInst(llvm::SelectInst& i) {
  processInstruction(i);
  string x = rep->id(&i);
  const Expr
  *c = rep->expr(i.getOperand(0)),
   *v1 = rep->expr(i.getOperand(1)),
    *v2 = rep->expr(i.getOperand(2));

  currBlock->addStmt(Stmt::havoc(x));
  currBlock->addStmt(Stmt::assume(Expr::and_(
                                    Expr::impl(c, Expr::eq(Expr::id(x), v1)),
                                    Expr::impl(Expr::not_(c), Expr::eq(Expr::id(x), v2))
                                  )));
}

void SmackInstGenerator::visitMemCpyInst(llvm::MemCpyInst& mci) {
  processInstruction(mci);
  unsigned dstReg = rep->getRegion(mci.getOperand(0));
  unsigned srcReg = rep->getRegion(mci.getOperand(1));

  vector<const Expr*> args;
  for (unsigned i = 0; i < mci.getNumOperands() - 1; i++)
    args.push_back(rep->expr(mci.getOperand(i)));
  assert(args.size() == 5);
  currBlock->addStmt(Stmt::call(rep->memcpyCall(dstReg,srcReg), args));
  moreDecls.insert(rep->memcpyProc(dstReg,srcReg));
}
} // namespace smack

