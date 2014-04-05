//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/SmackInstGenerator.h"
#include "smack/SmackOptions.h"
#include "llvm/InstVisitor.h"
#include "llvm/DebugInfo.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Support/GraphWriter.h"
#include <sstream>

#include <iostream>

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
  Block* b = new Block(proc, s.str());
  proc.addBlock(b);
  return b;
}

string SmackInstGenerator::createVar() {
  stringstream s;
  s << "$x" << varNum++;
  string name = s.str();
  proc.addDecl(Decl::variable(name, rep.getPtrType()));
  return name;
}

void SmackInstGenerator::nameInstruction(llvm::Instruction& inst) {
  if (!inst.getType()->isVoidTy()) {
    if (!inst.hasName() || !rep.isSmackGeneratedName(inst.getName())) {
      if (rep.isBool(&inst))
        inst.setName(SmackRep::BOOL_VAR);
      else if (rep.isFloat(&inst))
        inst.setName(SmackRep::FLOAT_VAR);
      else
        inst.setName(SmackRep::PTR_VAR);
    }
    proc.addDecl(Decl::variable(rep.id(&inst), rep.type(&inst)));
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
                             rep.expr(phi), rep.expr(v)));
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

/******************************************************************************/
/*                 TERMINATOR                  INSTRUCTIONS                   */
/******************************************************************************/

void SmackInstGenerator::visitReturnInst(llvm::ReturnInst& ri) {
  processInstruction(ri);

  if (llvm::Value* v = ri.getReturnValue())
    currBlock->addStmt(Stmt::assign(
                         Expr::id(SmackRep::RET_VAR), rep.expr(v)));

  currBlock->addStmt(Stmt::return_());
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

    const Expr* e = rep.expr(bi.getCondition());
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

  const Expr* e = rep.expr(si.getCondition());
  const Expr* n = Expr::lit(true);

  for (llvm::SwitchInst::CaseIt
       i = si.case_begin(); i != si.case_begin(); ++i) {

    assert(blockMap.count(i.getCaseSuccessor()) != 0);
    const Expr* v = rep.expr(i.getCaseValue());
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

void SmackInstGenerator::visitUnreachableInst(llvm::UnreachableInst& ii) {
  processInstruction(ii);
  
  currBlock->addStmt(Stmt::assume(Expr::lit(false)));
}

/******************************************************************************/
/*                   BINARY                    OPERATIONS                     */
/******************************************************************************/

void SmackInstGenerator::visitBinaryOperator(llvm::BinaryOperator& bo) {
  processInstruction(bo);
  currBlock->addStmt(Stmt::assign(rep.expr(&bo), rep.op(&bo)));
}

/******************************************************************************/
/*                   VECTOR                    OPERATIONS                     */
/******************************************************************************/

// TODO implement vector operations

/******************************************************************************/
/*                  AGGREGATE                   OPERATIONS                    */
/******************************************************************************/

// TODO implement aggregate operations

/******************************************************************************/
/*     MEMORY       ACCESS        AND       ADDRESSING       OPERATIONS       */
/******************************************************************************/

void SmackInstGenerator::visitAllocaInst(llvm::AllocaInst& ai) {
  processInstruction(ai);
  unsigned typeSize = rep.storageSize(ai.getAllocatedType());
  llvm::Value* arraySize = ai.getArraySize();
  currBlock->addStmt(Stmt::call(
                       SmackRep::ALLOCA,
                       Expr::fn(SmackRep::MUL, rep.lit(typeSize), rep.lit(arraySize)),
                       rep.id(&ai)));
}

void SmackInstGenerator::visitLoadInst(llvm::LoadInst& li) {
  processInstruction(li);
  const Expr* src = rep.mem(li.getPointerOperand());
  if (rep.isFloat(&li))
    src = rep.si2fp(src);
  currBlock->addStmt(Stmt::assign(rep.expr(&li),src));

  if (SmackOptions::MemoryModelDebug) {
    currBlock->addStmt(Stmt::call(SmackRep::REC_MEM_OP, Expr::id(SmackRep::MEM_OP_VAL)));
    currBlock->addStmt(Stmt::call("boogie_si_record_int", Expr::lit(0)));
    currBlock->addStmt(Stmt::call("boogie_si_record_int", rep.expr(li.getPointerOperand())));
    currBlock->addStmt(Stmt::call("boogie_si_record_int", rep.expr(&li)));
  }
}

void SmackInstGenerator::visitStoreInst(llvm::StoreInst& si) {
  processInstruction(si);
  const Expr* src = rep.expr(si.getOperand(0));
  if (rep.isFloat(si.getOperand(0)))
    src = rep.fp2si(src);
  currBlock->addStmt(Stmt::assign(rep.mem(si.getPointerOperand()),src));
                       
  if (SmackOptions::MemoryModelDebug) {
    currBlock->addStmt(Stmt::call(SmackRep::REC_MEM_OP, Expr::id(SmackRep::MEM_OP_VAL)));
    currBlock->addStmt(Stmt::call("boogie_si_record_int", Expr::lit(1)));
    currBlock->addStmt(Stmt::call("boogie_si_record_int", rep.expr(si.getPointerOperand())));
    currBlock->addStmt(Stmt::call("boogie_si_record_int", rep.expr(si.getOperand(0))));
  }
}

void SmackInstGenerator::visitAtomicCmpXchgInst(llvm::AtomicCmpXchgInst& i) {
  processInstruction(i);
  const Expr* res = rep.expr(&i);
  const Expr* ptr = rep.mem(i.getOperand(0));
  const Expr* cmp = rep.expr(i.getOperand(1));
  const Expr* swp = rep.expr(i.getOperand(2));
  currBlock->addStmt(Stmt::assign(res,ptr));
  currBlock->addStmt(Stmt::assign(ptr,Expr::cond(Expr::eq(ptr,cmp),swp,ptr)));
}

void SmackInstGenerator::visitAtomicRMWInst(llvm::AtomicRMWInst& i) {
  processInstruction(i);
  
  const Expr* res = rep.expr(&i);
  const Expr* mem = rep.mem(i.getPointerOperand());
  const Expr* val = rep.expr(i.getValOperand());  
  const Expr* op;  
  
  switch (i.getOperation()) {
    using llvm::AtomicRMWInst;
  case AtomicRMWInst::Xchg:
    op = val;
    break;
  case AtomicRMWInst::Add:
    op = Expr::fn(SmackRep::ADD,mem,val);
    break;
  case AtomicRMWInst::Sub:
    op = Expr::fn(SmackRep::SUB,mem,val);
    break;
  case AtomicRMWInst::And:
    op = Expr::fn(SmackRep::AND,mem,val);
    break;
  case AtomicRMWInst::Nand:
    op = Expr::fn(SmackRep::NAND,mem,val);
    break;
  case AtomicRMWInst::Or:
    op = Expr::fn(SmackRep::OR,mem,val);
    break;
  case AtomicRMWInst::Xor:
    op = Expr::fn(SmackRep::XOR,mem,val);
    break;
  case AtomicRMWInst::Max:
    op = Expr::fn(SmackRep::MAX,mem,val);
    break;
  case AtomicRMWInst::Min:
    op = Expr::fn(SmackRep::MIN,mem,val);
    break;
  case AtomicRMWInst::UMax:
    op = Expr::fn(SmackRep::UMAX,mem,val);
    break;
  case AtomicRMWInst::UMin:
    op = Expr::fn(SmackRep::UMIN,mem,val);
    break;
  default:
    assert(false && "unexpected atomic operation.");
  }  
  
  currBlock->addStmt(Stmt::assign(res,mem));
  currBlock->addStmt(Stmt::assign(mem,op));
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
  currBlock->addStmt(Stmt::assign(rep.expr(&gepi),
                                  rep.ptrArith(gepi.getPointerOperand(), ps, ts)));
}

/******************************************************************************/
/*                 CONVERSION                    OPERATIONS                   */
/******************************************************************************/

void SmackInstGenerator::visitTruncInst(llvm::TruncInst& ti) {
  processInstruction(ti);
  currBlock->addStmt(Stmt::assign(rep.expr(&ti),
    rep.trunc(rep.expr(ti.getOperand(0)), ti.getType())));
}

void SmackInstGenerator::visitZExtInst(llvm::ZExtInst& ci) {
  processInstruction(ci);

  const Expr* e = rep.expr(ci.getOperand(0));
  if (rep.isBool(ci.getSrcTy())) e = rep.b2p(e);
  currBlock->addStmt(Stmt::assign(rep.expr(&ci), e));
}

void SmackInstGenerator::visitSExtInst(llvm::SExtInst& ci) {
  processInstruction(ci);

  const Expr* e = rep.expr(ci.getOperand(0));
  if (rep.isBool(ci.getSrcTy())) e = rep.b2p(e);
  currBlock->addStmt(Stmt::assign(rep.expr(&ci), e));
}

void SmackInstGenerator::visitFPTruncInst(llvm::FPTruncInst& i) {
  processInstruction(i);
  WARN("not really handling floating point : " + i2s(i));
  currBlock->addStmt(Stmt::assign(rep.expr(&i), rep.expr(i.getOperand(0))));  
}

void SmackInstGenerator::visitFPExtInst(llvm::FPExtInst& i) {
  processInstruction(i);
  WARN("not really handling floating point : " + i2s(i));
  currBlock->addStmt(Stmt::assign(rep.expr(&i), rep.expr(i.getOperand(0))));
}

void SmackInstGenerator::visitFPToUIInst(llvm::FPToUIInst& i) {
  processInstruction(i);
  WARN("not really handling floating point : " + i2s(i));
  currBlock->addStmt(Stmt::assign(rep.expr(&i), 
    rep.fp2ui(rep.expr(i.getOperand(0)))));
}

void SmackInstGenerator::visitFPToSIInst(llvm::FPToSIInst& i) {
  processInstruction(i);
  WARN("not really handling floating point : " + i2s(i));
  currBlock->addStmt(Stmt::assign(rep.expr(&i), 
    rep.fp2si(rep.expr(i.getOperand(0)))));
}

void SmackInstGenerator::visitUIToFPInst(llvm::UIToFPInst& i) {
  processInstruction(i);
  WARN("not really handling floating point : " + i2s(i));
  currBlock->addStmt(Stmt::assign(rep.expr(&i), 
    rep.ui2fp(rep.expr(i.getOperand(0)))));
}

void SmackInstGenerator::visitSIToFPInst(llvm::SIToFPInst& i) {
  processInstruction(i);
  WARN("not really handling floating point : " + i2s(i));
  currBlock->addStmt(Stmt::assign(rep.expr(&i), 
    rep.si2fp(rep.expr(i.getOperand(0)))));
}

void SmackInstGenerator::visitPtrToIntInst(llvm::PtrToIntInst& i) {
  processInstruction(i);
  currBlock->addStmt(Stmt::assign(rep.expr(&i),
    rep.p2i(rep.expr(i.getOperand(0)))));
}

void SmackInstGenerator::visitIntToPtrInst(llvm::IntToPtrInst& i) {
  processInstruction(i);
  currBlock->addStmt(Stmt::assign(rep.expr(&i),
    rep.i2p(rep.expr(i.getOperand(0)))));
}

void SmackInstGenerator::visitBitCastInst(llvm::BitCastInst& ci) {
  processInstruction(ci);
  currBlock->addStmt(Stmt::assign(rep.expr(&ci), rep.expr(ci.getOperand(0))));
}

/******************************************************************************/
/*                   OTHER                     OPERATIONS                     */
/******************************************************************************/

void SmackInstGenerator::visitICmpInst(llvm::ICmpInst& ci) {
  processInstruction(ci);
  currBlock->addStmt(Stmt::assign(rep.expr(&ci), rep.pred(ci)));
}

void SmackInstGenerator::visitFCmpInst(llvm::FCmpInst& ci) {
  processInstruction(ci);
  WARN("floating point?!?!");
  currBlock->addStmt(Stmt::assign(rep.expr(&ci), rep.pred(ci)));
}

void SmackInstGenerator::visitPHINode(llvm::PHINode& phi) {
  // NOTE: this is really a No-Op, since assignments to the phi nodes
  // are handled in the translation of branch/switch instructions.
  processInstruction(phi);
}

void SmackInstGenerator::visitSelectInst(llvm::SelectInst& i) {
  processInstruction(i);
  string x = rep.id(&i);
  const Expr
  *c = rep.expr(i.getOperand(0)),
   *v1 = rep.expr(i.getOperand(1)),
    *v2 = rep.expr(i.getOperand(2));

  currBlock->addStmt(Stmt::havoc(x));
  currBlock->addStmt(Stmt::assume(Expr::and_(
                                    Expr::impl(c, Expr::eq(Expr::id(x), v1)),
                                    Expr::impl(Expr::not_(c), Expr::eq(Expr::id(x), v2))
                                  )));
}

void SmackInstGenerator::visitCallInst(llvm::CallInst& ci) {
  processInstruction(ci);
  
  llvm::Function* f = ci.getCalledFunction();

  if (ci.isInlineAsm()) {
    WARN("unsoundly ignoring inline asm call: " + i2s(ci));
    currBlock->addStmt(Stmt::skip());
    
  } else if (f && rep.id(f).find("llvm.dbg.") != string::npos) {
    WARN("ignoring llvm.debug call.");
    currBlock->addStmt(Stmt::skip());

  } else if (f && rep.id(f) == "__SMACK_mod") {
    proc.addMod(rep.code(ci));

  } else if (f && rep.id(f) == "__SMACK_code") {
    currBlock->addStmt(Stmt::code(rep.code(ci)));

  } else if (f && rep.id(f) == "__SMACK_decl") {
    proc.addDecl(Decl::code(rep.code(ci)));

  } else if (f && rep.id(f) == "__SMACK_top_decl") {
    proc.getProg().addDecl(Decl::code(rep.code(ci)));

  } else if (f) {
    currBlock->addStmt(rep.call(f, ci));

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
          currBlock->addStmt(rep.call(castFunc, ci));
          if (castFunc->isDeclaration() && rep.isExternal(&ci))
            currBlock->addStmt(Stmt::assume(Expr::fn("$isExternal",rep.expr(&ci))));
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
      if (f->getFunctionType() == t && f->hasAddressTaken())
        fs.push_back(f);

    if (fs.size() == 1) {
      // Q: is this case really possible?
      currBlock->addStmt(rep.call(fs[0], ci));

    } else if (fs.size() > 1) {
      Block* tail = createBlock();
      vector<string> targets;

      // Create a sequence of dispatch blocks, one for each call.
      for (unsigned i = 0; i < fs.size(); i++) {
        Block* disp = createBlock();
        targets.push_back(disp->getName());

        disp->addStmt(Stmt::assume(
                        Expr::eq(rep.expr(c), rep.expr(fs[i]))));
        disp->addStmt(rep.call(fs[i], ci));
        disp->addStmt(Stmt::goto_(tail->getName()));
      }

      // Jump to the dispatch blocks.
      currBlock->addStmt(Stmt::goto_(targets));

      // Update the current block for subsequent visits.
      currBlock = tail;

    } else {
      // In the worst case, we have no idea what function may have
      // been called...
      WARN("unsoundly ignoring indeterminate call: " + i2s(ci));
      currBlock->addStmt(Stmt::skip());
    }
  }

  if (f && f->isDeclaration() && rep.isExternal(&ci))
    currBlock->addStmt(Stmt::assume(Expr::fn("$isExternal",rep.expr(&ci))));
}

/******************************************************************************/
/*                  INTRINSIC                    FUNCTIONS                    */
/******************************************************************************/

void SmackInstGenerator::visitMemCpyInst(llvm::MemCpyInst& mci) {
  processInstruction(mci);
  unsigned dstReg = rep.getRegion(mci.getOperand(0));
  unsigned srcReg = rep.getRegion(mci.getOperand(1));

  vector<const Expr*> args;
  for (unsigned i = 0; i < mci.getNumOperands() - 1; i++)
    args.push_back(rep.expr(mci.getOperand(i)));
  assert(args.size() == 5);
  currBlock->addStmt(Stmt::call(rep.memcpyCall(dstReg,srcReg), args));
}

} // namespace smack
