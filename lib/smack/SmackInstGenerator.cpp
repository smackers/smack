//
// This file is distributed under the MIT License. See LICENSE for details.
//
#define DEBUG_TYPE "smack-inst-gen"
#include "smack/SmackInstGenerator.h"
#include "smack/BoogieAst.h"
#include "smack/Debug.h"
#include "smack/Naming.h"
#include "smack/SmackOptions.h"
#include "smack/SmackRep.h"
#include "smack/VectorOperations.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/FloatingPointMode.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstVisitor.h"
#include <fstream>
#include "llvm/Support/GraphWriter.h"
#include "smack/Regions.h"
#include <regex>
#include <sstream>

#include "llvm/Support/raw_ostream.h"
#include <iostream>

#include "smack/SmackWarnings.h"

namespace smack {

using llvm::errs;
using namespace llvm;

const bool SHOW_ORIG = false;

#define ORIG(ins)                                                              \
  if (SHOW_ORIG)                                                               \
  emit(Stmt::comment(i2s(ins)))

Regex VAR_DECL("^[[:space:]]*var[[:space:]]+([[:alpha:]_.$#'`~^\\?][[:alnum:]_."
               "$#'`~^\\?]*):.*;");

// Procedures whose return value should not be marked as external
Regex EXTERNAL_PROC_IGNORE("^(malloc|__VERIFIER_nondet)$");

std::string i2s(const llvm::Instruction &i) {
  std::string s;
  llvm::raw_string_ostream ss(s);
  ss << i;
  s = s.substr(2);
  return s;
}

Type *getElemType(const Type *t, unsigned idx) {
  if (const llvm::StructType *st = llvm::dyn_cast<const llvm::StructType>(t))
    return st->getElementType(idx);
  else if (const llvm::ArrayType *at = llvm::dyn_cast<const llvm::ArrayType>(t))
    return at->getElementType();
  else
    llvm_unreachable("Unexpected aggregate type.");
}

void SmackInstGenerator::emit(const Stmt *s) {
  // stringstream str;
  // s->print(str);
  // SDEBUG(llvm::errs() << "emit:   " << str.str() << "\n");
  currBlock->addStmt(s);
}

const Stmt *
SmackInstGenerator::recordProcedureCall(const llvm::Value *V,
                                        std::list<const Attr *> attrs) {
  auto D = Decl::procedure("boogie_si_record_" + rep->type(V),
                           {{"x", rep->type(V)}});
  rep->addAuxiliaryDeclaration(D);
  return Stmt::call(D->getName(), {rep->expr(V)}, {}, attrs);
}

Block *SmackInstGenerator::createBlock() {
  Block *b = Block::block(naming->freshBlockName());
  proc->getBlocks().push_back(b);
  return b;
}

Block *SmackInstGenerator::getBlock(llvm::BasicBlock *bb) {
  if (blockMap.count(bb) == 0)
    blockMap[bb] = createBlock();
  return blockMap[bb];
}

std::string SmackInstGenerator::blockName(const llvm::BasicBlock *bb) const {
  auto it = blockMap.find(bb);
  return it == blockMap.end() ? "" : it->second->getName();
}

void SmackInstGenerator::nameInstruction(llvm::Instruction &inst) {
  if (inst.getType()->isVoidTy())
    return;
  proc->getDeclarations().push_back(
      Decl::variable(naming->get(inst), rep->type(&inst)));
}

void SmackInstGenerator::hoistLoopStmtToHeader(const llvm::Loop *loop,
                                               const Stmt *stmt) {
  hoistLoopStmtsToHeader(loop, {stmt});
}

void SmackInstGenerator::hoistLoopStmtsToHeader(
    const llvm::Loop *loop, std::list<const Stmt *> stmtsToHoist) {
  if (!loop) {
    for (auto *stmt : stmtsToHoist)
      emit(stmt);
    return;
  }

  auto *header = loop->getHeader();
  if (!header || !blockMap.count(header)) {
    for (auto *stmt : stmtsToHoist)
      emit(stmt);
    return;
  }

  auto &stmts = blockMap[header]->getStatements();
  auto insertAt = stmts.begin();

  if (insertAt != stmts.end()) {
    if (auto *assume = llvm::dyn_cast<const AssumeStmt>(*insertAt)) {
      if (assume->hasAttr("loop_header"))
        ++insertAt;
    }
  }

  while (insertAt != stmts.end() &&
         (*insertAt)->getKind() == Stmt::ASSIGN) {
    ++insertAt;
  }

  for (auto *stmt : stmtsToHoist) {
    insertAt = stmts.insert(insertAt, stmt);
    ++insertAt;
  }
}

const llvm::Loop *
SmackInstGenerator::invariantLoopForHeader(
    const llvm::BasicBlock *header) const {
  for (auto *loop = loops.getLoopFor(header); loop;
       loop = loop->getParentLoop()) {
    if (loop->getHeader() == header && loopInvariants.count(loop))
      return loop;
  }
  return nullptr;
}

void SmackInstGenerator::addLoopInvariantChecks(Block *block,
                                                const llvm::Loop *loop) {
  if (!loop)
    return;

  for (auto &I : *loop->getHeader()) {
    if (auto *phi = llvm::dyn_cast<llvm::PHINode>(&I)) {
      std::string phiName = naming->get(*phi);
      block->addStmt(
          Stmt::assign(Expr::id(phiName + ".pre"), Expr::id(phiName)));
    }
  }

  auto *attr = Attr::attr(Naming::LOOP_INVARIANT_ANNOTATION);
  for (auto *expr : loopInvariants[loop])
    block->addStmt(Stmt::assert_(expr, {attr}));
}

std::string SmackInstGenerator::getSourceLine(const std::string &filename,
                                               unsigned line) {
  if (line == 0)
    return "";
  auto it = sourceLineCache.find(filename);
  if (it == sourceLineCache.end()) {
    // Try to read the file from multiple candidate paths
    std::vector<std::string> lines;
    std::vector<std::string> candidates = {
      filename,
      "../" + filename,           // from build/ up to examples/
      "../../" + filename,        // from build/ up to project root
    };
    for (auto &path : candidates) {
      std::ifstream ifs(path);
      if (ifs.is_open()) {
        std::string l;
        while (std::getline(ifs, l))
          lines.push_back(l);
        break;
      }
    }
    it = sourceLineCache.emplace(filename, std::move(lines)).first;
  }
  auto &lines = it->second;
  if (line <= lines.size()) {
    // Trim leading/trailing whitespace
    std::string s = lines[line - 1];
    size_t start = s.find_first_not_of(" \t");
    if (start == std::string::npos)
      return "";
    size_t end = s.find_last_not_of(" \t\r\n");
    return s.substr(start, end - start + 1);
  }
  return "";
}

unsigned SmackInstGenerator::instructionIndex(const llvm::Instruction &I) const {
  unsigned index = 0;
  if (!I.getParent())
    return index;

  for (auto &Other : *I.getParent()) {
    if (&Other == &I)
      return index;
    if (!llvm::isa<llvm::DbgInfoIntrinsic>(Other))
      index++;
  }
  return index;
}

std::string SmackInstGenerator::llvmInstructionId(
    const llvm::Instruction &I) const {
  std::stringstream id;
  id << (I.getFunction() ? naming->get(*I.getFunction()) : "<nofunc>");
  id << ":";
  id << (I.getParent() ? naming->get(*I.getParent()) : "<nobb>");
  id << ":";
  id << instructionIndex(I);
  return id.str();
}

void SmackInstGenerator::annotate(llvm::Instruction &I, Block *B) {

  // do not generate sourceloc from calls to llvm.debug since
  // those point to variable declaration lines and such
  if (llvm::CallInst *ci = llvm::dyn_cast<llvm::CallInst>(&I)) {
    llvm::Function *f = ci->getCalledFunction();
    std::string name = f && f->hasName() ? f->getName().str() : "";
    if (name.find("llvm.dbg.") != std::string::npos) {
      return;
    }
  }

  if (SmackOptions::SourceLocSymbols && I.getMetadata("dbg")) {
    const DebugLoc DL = I.getDebugLoc();
    auto *scope = cast<DIScope>(DL.getScope());
    std::string filename = scope->getFilename().str();
    unsigned line = DL.getLine();
    B->addStmt(Stmt::annot(Attr::attr("sourceloc", filename,
                                      line, DL.getCol())));
    // Embed the actual C source line text
    std::string srcLine = getSourceLine(filename, line);
    if (!srcLine.empty()) {
      B->addStmt(Stmt::annot(Attr::attr("c_line", srcLine)));
    }
  }

  if (SmackOptions::ProvenanceSymbols) {
    std::string func = I.getFunction() ? naming->get(*I.getFunction()) : "";
    std::string bb = I.getParent() ? naming->get(*I.getParent()) : "";
    std::list<const Attr *> attrs;
    attrs.push_back(Attr::attr("llvm.func", func));
    attrs.push_back(Attr::attr("llvm.bb", bb));
    attrs.push_back(Attr::attr("llvm.inst", llvmInstructionId(I)));
    attrs.push_back(Attr::attr("llvm.op", I.getOpcodeName()));
    B->addStmt(Stmt::annot(attrs));
  }

  // https://stackoverflow.com/questions/22138947/reading-metadata-from-instruction
  SmallVector<std::pair<unsigned, MDNode *>, 4> MDForInst;
  I.getAllMetadata(MDForInst);
  SmallVector<StringRef, 8> Names;
  I.getModule()->getMDKindNames(Names);

  //  for(auto II = MDForInst.begin(), EE = MDForInst.end(); II !=EE; ++II) {
  for (auto II : MDForInst) {
    StringRef name = Names[II.first];
    if (name.find("smack.") == 0 || name.find("verifier.") == 0) {
      std::list<const Expr *> attrs;
      for (auto AI = II.second->op_begin(), AE = II.second->op_end(); AI != AE;
           ++AI) {
        if (auto *CI = mdconst::dyn_extract<ConstantInt>(*AI)) {
          auto value = CI->getZExtValue();
          attrs.push_back(Expr::lit((long long)value));
        } else if (auto *CI = dyn_cast<MDString>(*AI)) {
          auto value = CI->getString();
          attrs.push_back(Expr::lit(value.str()));
        } else {
          llvm_unreachable("unexpected attribute type in smack metadata");
        }
      }
      B->addStmt(Stmt::annot(Attr::attr(name.str(), attrs)));
    }
  }
}

void SmackInstGenerator::processInstruction(llvm::Instruction &inst) {
  SDEBUG(errs() << "Inst: " << inst << "\n");
  annotate(inst, currBlock);
  ORIG(inst);
  nameInstruction(inst);
  nextInst++;
}

void SmackInstGenerator::visitBasicBlock(llvm::BasicBlock &bb) {
  nextInst = bb.begin();
  currBlock = getBlock(&bb);

  auto *F = bb.getParent();
  if (&bb == &F->getEntryBlock()) {
    for (auto &I : bb) {
      if (llvm::isa<llvm::DbgInfoIntrinsic>(I))
        continue;
      if (I.getDebugLoc()) {
        annotate(I, currBlock);
        break;
      }
    }
    if (SmackOptions::isEntryPoint(naming->get(*F))) {
      emit(recordProcedureCall(
          F, {Attr::attr("cexpr", "smack:entry:" + naming->get(*F))}));
      for (auto &A : F->args()) {
        emit(recordProcedureCall(
            &A, {Attr::attr("cexpr", "smack:arg:" + naming->get(*F) + ":" +
                                         naming->get(A))}));
      }
    }
  }

  // Loop structure annotations: mark headers and body blocks.
  // PHI disambiguation: for loop headers, emit .pre captures.
  // For loop body blocks, activate PHI-to-.pre renaming so body
  // instructions reference .pre instead of the PHI variables.
  llvm::Loop *L = loops.getLoopFor(&bb);
  if (L) {
    std::string headerName = getBlock(L->getHeader())->getName();
    if (L->getHeader() == &bb) {
      // Annotate as loop header
      emit(Stmt::annot(Attr::attr("loop_header", headerName)));

      // Loop header: emit $var.pre := $var for each PHI
      rep->clearPhiPreRenames();
      for (auto &I : bb) {
        if (auto *phi = llvm::dyn_cast<llvm::PHINode>(&I)) {
          std::string phiName = naming->get(*phi);
          std::string preName = phiName + ".pre";
          proc->getDeclarations().push_back(
              Decl::variable(preName, rep->type(phi)));
          emit(Stmt::assign(Expr::id(preName), Expr::id(phiName)));
        }
      }
    } else {
      // Annotate as loop body
      emit(Stmt::annot(Attr::attr("loop_body", headerName)));

      // Loop body block: activate PHI-to-.pre renaming
      rep->clearPhiPreRenames();
      for (auto &I : *L->getHeader()) {
        if (auto *phi = llvm::dyn_cast<llvm::PHINode>(&I)) {
          std::string preName = naming->get(*phi) + ".pre";
          rep->setPhiPreRename(phi, preName);
        }
      }
    }
  } else {
    rep->clearPhiPreRenames();
  }
}

void SmackInstGenerator::visitInstruction(llvm::Instruction &inst) {
  SDEBUG(errs() << "Instruction not handled: " << inst << "\n");
  llvm_unreachable("Instruction not handled.");
}

void SmackInstGenerator::generatePhiAssigns(llvm::Instruction &ti) {
  llvm::BasicBlock *block = ti.getParent();
  // Temporarily disable PHI renames for the PHI assignment itself;
  // the LHS must use the original PHI variable names, not .pre.
  auto savedRenames = rep->phiPreRenames;
  rep->clearPhiPreRenames();

  std::list<const Expr *> lhs;
  std::list<const Expr *> rhs;

  for (unsigned i = 0; i < ti.getNumSuccessors(); i++) {
    llvm::BasicBlock *successor = ti.getSuccessor(i);

    // write to the phi-node variable of the successor
    for (llvm::BasicBlock::iterator s = successor->begin(),
                                    e = successor->end();
         s != e && llvm::isa<llvm::PHINode>(s); ++s) {

      llvm::PHINode *phi = llvm::cast<llvm::PHINode>(s);
      if (llvm::Value *v = phi->getIncomingValueForBlock(block)) {
        v = v->stripPointerCastsAndAliases();
        lhs.push_back(rep->expr(phi));
        rhs.push_back(rep->expr(v));
      }
    }
  }
  if (!lhs.empty()) {
    emit(Stmt::assign(lhs, rhs));
  }

  // Restore renames
  rep->phiPreRenames = savedRenames;
}

void SmackInstGenerator::generateGotoStmts(
    llvm::Instruction &inst,
    std::vector<std::pair<const Expr *, llvm::BasicBlock *>> targets) {

  assert(targets.size() > 0);

  if (targets.size() > 1) {
    std::list<std::string> dispatch;

    for (unsigned i = 0; i < targets.size(); i++) {
      const Expr *condition = targets[i].first;
      llvm::BasicBlock *target = targets[i].second;
      auto *invariantLoop = invariantLoopForHeader(target);

      // Tag every branch-target assume with ``:partition``.  Boogie
      // already emits this attribute when it desugars structured
      // ``if`` / ``while`` constructs (BigBlocksResolutionContext.cs),
      // but SMACK lowers LLVM branches directly to goto+assume form,
      // bypassing that path.  Without the tag the verifier's data
      // back-slice can't recognise the assume as a branch condition
      // (``extract_condition_and_pc_from_block`` filters by attribute),
      // so reach-style proofs walk straight past every MAIN-level
      // branch and accumulate vacuous implications all the way back
      // to the alloc partitions.
      const Attr *partitionAttr = Attr::attr("partition");

      if (invariantLoop) {
        Block *b = createBlock();
        annotate(inst, b);
        b->addStmt(Stmt::assume(condition, partitionAttr));
        addLoopInvariantChecks(b, invariantLoop);
        b->addStmt(Stmt::goto_({getBlock(target)->getName()}));
        dispatch.push_back(b->getName());

      } else if (target->getUniquePredecessor() == inst.getParent()) {
        Block *b = getBlock(target);
        b->insert(Stmt::assume(condition, partitionAttr));
        dispatch.push_back(b->getName());

      } else {
        Block *b = createBlock();
        annotate(inst, b);
        b->addStmt(Stmt::assume(condition, partitionAttr));
        b->addStmt(Stmt::goto_({getBlock(target)->getName()}));
        dispatch.push_back(b->getName());
      }
    }

    emit(Stmt::goto_(dispatch));

  } else {
    auto *target = targets[0].second;
    auto *invariantLoop = invariantLoopForHeader(target);
    if (invariantLoop) {
      addLoopInvariantChecks(currBlock, invariantLoop);
    }
    emit(Stmt::goto_({getBlock(target)->getName()}));
  }
}

/******************************************************************************/
/*                 TERMINATOR                  INSTRUCTIONS                   */
/******************************************************************************/

void SmackInstGenerator::visitReturnInst(llvm::ReturnInst &ri) {
  processInstruction(ri);

  llvm::Value *v = ri.getReturnValue();
  if (v)
    emit(Stmt::assign(Expr::id(Naming::RET_VAR), rep->expr(v)));
  emit(Stmt::assign(Expr::id(Naming::EXN_VAR), Expr::lit(false)));
  emit(Stmt::return_());
}

void SmackInstGenerator::visitBranchInst(llvm::BranchInst &bi) {
  processInstruction(bi);

  // Collect the list of tarets
  std::vector<std::pair<const Expr *, llvm::BasicBlock *>> targets;

  if (bi.getNumSuccessors() == 1) {

    // Unconditional branch
    targets.push_back({Expr::lit(true), bi.getSuccessor(0)});

  } else {

    // Conditional branch
    assert(bi.getNumSuccessors() == 2);
    const Expr *e =
        Expr::eq(rep->expr(bi.getCondition()), rep->integerLit(1ULL, 1));
    targets.push_back({e, bi.getSuccessor(0)});
    targets.push_back({Expr::not_(e), bi.getSuccessor(1)});
  }
  generatePhiAssigns(bi);
  if (bi.getNumSuccessors() > 1)
    emit(Stmt::annot(Attr::attr(Naming::BRANCH_CONDITION_ANNOTATION,
                                {rep->expr(bi.getCondition())})));
  generateGotoStmts(bi, targets);
}

void SmackInstGenerator::visitSwitchInst(llvm::SwitchInst &si) {
  processInstruction(si);

  // Collect the list of tarets
  std::vector<std::pair<const Expr *, llvm::BasicBlock *>> targets;

  const Expr *e = rep->expr(si.getCondition());
  const Expr *n = Expr::lit(true);

  for (llvm::SwitchInst::CaseIt i = si.case_begin(); i != si.case_begin();
       ++i) {

    const Expr *v = rep->expr(i->getCaseValue());
    targets.push_back({Expr::eq(e, v), i->getCaseSuccessor()});

    // Add the negation of this case to the default case
    n = Expr::and_(n, Expr::neq(e, v));
  }

  // The default case
  targets.push_back({n, si.getDefaultDest()});

  generatePhiAssigns(si);
  emit(Stmt::annot(Attr::attr(Naming::BRANCH_CONDITION_ANNOTATION,
                              {rep->expr(si.getCondition())})));
  generateGotoStmts(si, targets);
}

void SmackInstGenerator::visitInvokeInst(llvm::InvokeInst &ii) {
  processInstruction(ii);
  llvm::Function *f = ii.getCalledFunction();
  if (f)
    emit(rep->call(f, ii));
  else
    llvm_unreachable("Unexpected invoke instruction.");

  std::vector<std::pair<const Expr *, llvm::BasicBlock *>> targets;
  targets.push_back(
      {Expr::not_(Expr::id(Naming::EXN_VAR)), ii.getNormalDest()});
  targets.push_back({Expr::id(Naming::EXN_VAR), ii.getUnwindDest()});
  emit(Stmt::annot(Attr::attr(Naming::BRANCH_CONDITION_ANNOTATION,
                              {Expr::id(Naming::EXN_VAR)})));
  generateGotoStmts(ii, targets);
}

void SmackInstGenerator::visitResumeInst(llvm::ResumeInst &ri) {
  processInstruction(ri);
  emit(Stmt::assign(Expr::id(Naming::EXN_VAR), Expr::lit(true)));
  emit(Stmt::assign(Expr::id(Naming::EXN_VAL_VAR), rep->expr(ri.getValue())));
  emit(Stmt::return_());
}

void SmackInstGenerator::visitUnreachableInst(llvm::UnreachableInst &ii) {
  processInstruction(ii);

  emit(Stmt::assume(Expr::lit(false)));
}

/******************************************************************************/
/*                   BINARY                    OPERATIONS                     */
/******************************************************************************/

void SmackInstGenerator::visitBinaryOperator(llvm::BinaryOperator &I) {
  processInstruction(I);
  if (rep->isBitwiseOp(&I) && I.getType()->getIntegerBitWidth() > 1)
    SmackWarnings::warnOverApproximate(
        std::string("bitwise operation ") + I.getOpcodeName(),
        {&SmackOptions::BitPrecise}, currBlock, &I);
  if (rep->isFpArithOp(&I))
    SmackWarnings::warnOverApproximate(
        std::string("floating-point operation ") + I.getOpcodeName(),
        {&SmackOptions::FloatEnabled}, currBlock, &I);

  const Expr *E;
  if (isa<FixedVectorType>(I.getType())) {
    auto X = I.getOperand(0);
    auto Y = I.getOperand(1);
    auto D = VectorOperations(rep).binary(&I);
    E = Expr::fn(D->getName(), {rep->expr(X), rep->expr(Y)});
  } else {
    E = rep->bop(&I);
  }
  emit(Stmt::assign(rep->expr(&I), E));
}

/******************************************************************************/
/*                   UNARY                    OPERATIONS                     */
/******************************************************************************/

void SmackInstGenerator::visitUnaryOperator(llvm::UnaryOperator &I) {
  assert(I.getOpcode() == Instruction::FNeg &&
         !isa<FixedVectorType>(I.getType()) && "Unsupported unary operation!");
  processInstruction(I);
  SmackWarnings::warnOverApproximate(
      std::string("floating-point operation ") + I.getOpcodeName(),
      {&SmackOptions::FloatEnabled}, currBlock, &I);
  emit(Stmt::assign(rep->expr(&I), rep->uop(&I)));
}

/******************************************************************************/
/*                   VECTOR                    OPERATIONS                     */
/******************************************************************************/

void SmackInstGenerator::visitExtractElementInst(ExtractElementInst &I) {
  processInstruction(I);
  auto X = I.getOperand(0);
  auto Y = I.getOperand(1);
  auto D = VectorOperations(rep).extract(X->getType(), Y->getType());
  emit(Stmt::assign(rep->expr(&I),
                    Expr::fn(D->getName(), {rep->expr(X), rep->expr(Y)})));
}

void SmackInstGenerator::visitInsertElementInst(InsertElementInst &I) {
  processInstruction(I);
  auto X = I.getOperand(0);
  auto Y = I.getOperand(1);
  auto Z = I.getOperand(2);
  auto D = VectorOperations(rep).insert(X->getType(), Z->getType());
  emit(Stmt::assign(
      rep->expr(&I),
      Expr::fn(D->getName(), {rep->expr(X), rep->expr(Y), rep->expr(Z)})));
}

void SmackInstGenerator::visitShuffleVectorInst(ShuffleVectorInst &I) {
  processInstruction(I);
  auto X = I.getOperand(0);
  auto Y = I.getOperand(1);
  auto M = I.getShuffleMask();
  std::vector<int> mask;
  for (auto idx : M)
    mask.push_back(idx);
  auto D = VectorOperations(rep).shuffle(X->getType(), I.getType(), mask);
  emit(Stmt::assign(rep->expr(&I),
                    Expr::fn(D->getName(), {rep->expr(X), rep->expr(Y)})));
}

/******************************************************************************/
/*                  AGGREGATE                   OPERATIONS                    */
/******************************************************************************/

void SmackInstGenerator::visitExtractValueInst(llvm::ExtractValueInst &evi) {
  processInstruction(evi);
  const Value *ao = evi.getAggregateOperand();
  const Expr *e = rep->expr(ao);
  const Type *t = ao->getType();

  for (auto &idx : evi.indices()) {
    e = Expr::fn(rep->opName(Naming::EXTRACT_VALUE, {getElemType(t, idx)}), e,
                 Expr::lit((unsigned long long)idx));
    t = getElemType(t, idx);
  }
  emit(Stmt::assign(rep->expr(&evi), e));
}

void SmackInstGenerator::visitInsertValueInst(llvm::InsertValueInst &ivi) {
  processInstruction(ivi);
  const Expr *old = rep->expr(ivi.getAggregateOperand());
  const Expr *res = rep->expr(&ivi);
  const llvm::Type *t = ivi.getType();

  auto getNumElements = [](const Type *t) -> unsigned {
    if (const llvm::StructType *st =
            llvm::dyn_cast<const llvm::StructType>(t)) {
      return st->getNumElements();
    } else if (const llvm::ArrayType *at =
                   llvm::dyn_cast<const llvm::ArrayType>(t)) {
      return at->getNumElements();
    } else {
      llvm_unreachable("Unexpected aggregate type.");
    }
  };

  for (auto &idx : ivi.indices()) {

    for (unsigned j = 0; j < getNumElements(t); j++) {
      if (j != idx) {
        emit(Stmt::assume(Expr::eq(
            Expr::fn(rep->opName(Naming::EXTRACT_VALUE, {getElemType(t, j)}),
                     res, Expr::lit(j)),
            Expr::fn(rep->opName(Naming::EXTRACT_VALUE, {getElemType(t, j)}),
                     old, Expr::lit(j)))));
      }
    }
    res = Expr::fn(rep->opName(Naming::EXTRACT_VALUE, {getElemType(t, idx)}),
                   res, Expr::lit(idx));
    old = Expr::fn(rep->opName(Naming::EXTRACT_VALUE, {getElemType(t, idx)}),
                   old, Expr::lit(idx));
    t = getElemType(t, idx);
  }
  emit(Stmt::assume(Expr::eq(res, rep->expr(ivi.getInsertedValueOperand()))));
}

/******************************************************************************/
/*     MEMORY       ACCESS        AND       ADDRESSING       OPERATIONS       */
/******************************************************************************/

void SmackInstGenerator::visitAllocaInst(llvm::AllocaInst &ai) {
  processInstruction(ai);
  emit(rep->alloca(ai));
}

void SmackInstGenerator::visitLoadInst(llvm::LoadInst &li) {
  processInstruction(li);
  auto P = li.getPointerOperand();
  assert(P->getType()->isPointerTy() && "expected pointer type");

  // TODO what happens with aggregate types?
  // assert (!li.getType()->isAggregateType() && "Unexpected load value.");

  const Expr *E;
  if (isa<FixedVectorType>(li.getType())) {
    unsigned R = rep->getRegions()->idx(li);
    auto D = VectorOperations(rep).load(R, P, li.getType());
    E = Expr::fn(D->getName(), {Expr::id(rep->memPath(R)), rep->expr(P)});
  } else {
    E = rep->load(li);
  }

  emit(Stmt::assign(rep->expr(&li), E));

  if (SmackOptions::MemoryModelDebug) {
    emit(Stmt::call(Naming::REC_MEM_OP, {Expr::id(Naming::MEM_OP_VAL)}));
    emit(recordProcedureCall(
        ConstantInt::get(Type::getInt32Ty(li.getContext()), 0), {}));
    emit(recordProcedureCall(P, {}));
    emit(recordProcedureCall(&li, {}));
  }
}

void SmackInstGenerator::visitStoreInst(llvm::StoreInst &si) {
  processInstruction(si);
  const llvm::Value *P = si.getPointerOperand();
  const llvm::Value *V = si.getValueOperand()->stripPointerCastsAndAliases();
  assert(!V->getType()->isAggregateType() && "Unexpected store value.");

  if (isa<FixedVectorType>(V->getType())) {
    unsigned R = rep->getRegions()->idx(si);
    auto D = VectorOperations(rep).store(R, P, V->getType());
    auto M = Expr::id(rep->memPath(R));
    auto E = Expr::fn(D->getName(), {M, rep->expr(P), rep->expr(V)});
    emit(Stmt::assign(M, E));
  } else {
    emit(rep->store(si));
    if (const Stmt *inverseAssume = rep->inverseFPCastAssume(&si)) {
      emit(inverseAssume);
    }
  }

  if (SmackOptions::SourceLocSymbols) {
    if (const llvm::GlobalVariable *G =
            llvm::dyn_cast<const llvm::GlobalVariable>(P)) {
      if (!G->getValueType()->isPointerTy() && G->hasName()) {
        emit(recordProcedureCall(V,
                                 {Attr::attr("cexpr", G->getName().str())}));
      }
    }
  }

  if (SmackOptions::MemoryModelDebug) {
    emit(Stmt::call(Naming::REC_MEM_OP, {Expr::id(Naming::MEM_OP_VAL)}));
    emit(recordProcedureCall(
        ConstantInt::get(Type::getInt32Ty(si.getContext()), 1), {}));
    emit(recordProcedureCall(P, {}));
    emit(recordProcedureCall(V, {}));
  }
}

void SmackInstGenerator::visitAtomicCmpXchgInst(llvm::AtomicCmpXchgInst &i) {
  processInstruction(i);
  const Expr *res = rep->expr(&i);
  const Expr *mem = rep->load(i.getOperand(0), i.getCompareOperand()->getType());
  const Expr *cmp = rep->expr(i.getOperand(1));
  const Expr *swp = rep->expr(i.getOperand(2));
  emit(Stmt::assign(res, mem));
  emit(rep->store(i.getOperand(0), i.getCompareOperand()->getType(),
                  Expr::ifThenElse(Expr::eq(mem, cmp), swp, mem)));
}

void SmackInstGenerator::visitAtomicRMWInst(llvm::AtomicRMWInst &i) {
  using llvm::AtomicRMWInst;
  processInstruction(i);
  const Expr *res = rep->expr(&i);
  const Expr *mem = rep->load(i.getPointerOperand(), i.getValOperand()->getType());
  const Expr *val = rep->expr(i.getValOperand());
  auto valT = rep->type(i.getValOperand()->getType());
  emit(Stmt::assign(res, mem));
  emit(rep->store(i.getPointerOperand(), i.getValOperand()->getType(),
                  i.getOperation() == AtomicRMWInst::Xchg
                      ? val
                      : Expr::fn(indexedName(Naming::ATOMICRMWINST_TABLE.at(
                                                 i.getOperation()),
                                             {valT}),
                                 mem, val)));
}

void SmackInstGenerator::visitGetElementPtrInst(llvm::GetElementPtrInst &I) {
  processInstruction(I);
  emit(Stmt::assign(rep->expr(&I), rep->ptrArith(&I)));
}

/******************************************************************************/
/*                 CONVERSION                    OPERATIONS                   */
/******************************************************************************/

void SmackInstGenerator::visitCastInst(llvm::CastInst &I) {
  if (isa<BitCastInst>(I) && I.getSrcTy()->isPointerTy() && I.getDestTy()->isPointerTy()) {
    return;
  }

  processInstruction(I);
  const Expr *E;
  if (isa<FixedVectorType>(I.getType())) {
    auto X = I.getOperand(0);
    auto D = VectorOperations(rep).cast(&I);
    E = Expr::fn(D->getName(), rep->expr(X));
  } else {
    E = rep->cast(&I);
  }
  emit(Stmt::assign(rep->expr(&I), E));

  if (I.getOpcode() == Instruction::BitCast) {
    if (const Stmt *inverseAssume =
            rep->inverseFPCastAssume(I.getOperand(0), I.getType())) {
      emit(inverseAssume);
    }
  }
}

/******************************************************************************/
/*                   OTHER                     OPERATIONS                     */
/******************************************************************************/

void SmackInstGenerator::visitCmpInst(llvm::CmpInst &I) {
  processInstruction(I);
  const Expr *E;
  if (isa<FixedVectorType>(I.getType())) {
    auto X = I.getOperand(0);
    auto Y = I.getOperand(1);
    auto D = VectorOperations(rep).cmp(&I);
    E = Expr::fn(D->getName(), rep->expr(X), rep->expr(Y));
  } else {
    E = rep->cmp(&I);
  }
  emit(Stmt::assign(rep->expr(&I), E));
}

void SmackInstGenerator::visitPHINode(llvm::PHINode &phi) {
  // NOTE: this is really a No-Op, since assignments to the phi nodes
  // are handled in the translation of branch/switch instructions.
  processInstruction(phi);
}

void SmackInstGenerator::visitSelectInst(llvm::SelectInst &i) {
  processInstruction(i);
  std::string x = naming->get(i);
  emit(Stmt::assign(Expr::id(x), rep->select(&i)));
}

void SmackInstGenerator::visitCallInst(llvm::CallInst &ci) {
  processInstruction(ci);

  if (ci.isInlineAsm()) {
    SmackWarnings::warnApproximate("inline asm call " + i2s(ci), currBlock,
                                   &ci);
    emit(Stmt::skip());
    return;
  }

  Function *f = ci.getCalledFunction();
  if (!f) {
    assert(ci.getCalledOperand() && "Called value is null");
    f = cast<Function>(ci.getCalledOperand()->stripPointerCastsAndAliases());
  }

  StringRef name = f->hasName() ? f->getName() : "";

  if (SmackOptions::RustPanics && name == Naming::RUST_PANIC_MARKER &&
      SmackOptions::shouldCheckFunction(
          ci.getParent()->getParent()->getName())) {
    // Convert Rust's panic functions into assertion violations
    emit(Stmt::assert_(Expr::lit(false),
                       {Attr::attr(Naming::RUST_PANIC_ANNOTATION)}));
  } else if (name == "__VERIFIER_assert" &&
             !SmackOptions::shouldCheckFunction(
                 ci.getParent()->getParent()->getName())) {
    // Skip this assertion if we shouldn't check in the parent function
    return;

  } else if (name == "__VERIFIER_assume" && ci.arg_size() == 1) {
    // Emit assume directly in the caller, without inline procedure indirection.
    // This keeps the assume's variable in the caller's scope so the
    // backslice can trace constraints back to the original parameters.
    const Expr *arg = rep->expr(ci.getArgOperand(0));
    emit(Stmt::assume(Expr::neq(arg, Expr::id("$0"))));
    return;

  } else if (name == "__VERIFIER_assert" &&
             SmackOptions::shouldCheckFunction(
                 ci.getParent()->getParent()->getName()) &&
             ci.arg_size() == 1) {
    // Emit assert directly in the caller, same as assume but for asserts.
    const Expr *arg = rep->expr(ci.getArgOperand(0));
    emit(Stmt::assert_(Expr::neq(arg, Expr::id("$0"))));
    return;

  } else if (name.find(Naming::VALUE_PROC) != StringRef::npos) {
    emit(rep->valueAnnotation(ci));

  } else if (name.find(Naming::RETURN_VALUE_PROC) != StringRef::npos) {
    emit(rep->returnValueAnnotation(ci));

  } else if (name.find(Naming::MOD_PROC) != StringRef::npos) {
    proc->getModifies().push_back(rep->code(ci));

  } else if (name.find(Naming::CODE_PROC) != StringRef::npos) {
    std::string boogieCode = rep->code(ci);

    for (unsigned i = 0; i < ci.arg_size(); ++i) {
      llvm::Value *arg = ci.getArgOperand(i);

      if (!arg || !arg->getType()->isPointerTy())
        continue;

      std::stringstream ss;
      rep->expr(arg)->print(ss);
      std::string boogieVar = ss.str();
      std::string searchToken = "MEM(" + boogieVar + ")";

      if (boogieCode.find(searchToken) != std::string::npos) {
        unsigned regionId = rep->getRegions()->idx(arg);
        std::string mapName = "$M." + std::to_string(regionId);

        size_t pos = 0;
        while ((pos = boogieCode.find(searchToken, pos)) != std::string::npos) {
          boogieCode.replace(pos, searchToken.length(), mapName);
          pos += mapName.length();
        }
      }
    }

    // Fix SMACK inconsistency: some constant args are emitted as "2bv64"
    // instead of "2".  Boogie rejects bv64 in ref-typed contexts ($add.ref,
    // $mul.ref). Normalize NNNbv64 to NNN in the generated code string.
    {
      std::regex bvRe("([0-9]+)bv64");
      boogieCode = std::regex_replace(boogieCode, bvRe, "$1");
    }

    auto L = loops[ci.getParent()];

    if (L && boogieCode.find("ptr_counter") != std::string::npos) {
      std::string storeAddrs;
      for (auto *BB : L->blocks()) {
        for (auto &I : *BB) {
          if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
            llvm::Value *ptr = SI->getPointerOperand();
            if (llvm::isa<llvm::GetElementPtrInst>(ptr) ||
                llvm::isa<llvm::PHINode>(ptr)) {
              std::stringstream ss;
              rep->expr(ptr)->print(ss);
              std::string name = ss.str();
              if (name.find(".shadow") == std::string::npos &&
                  storeAddrs.find(name) == std::string::npos) {
                if (!storeAddrs.empty())
                  storeAddrs += ", ";
                storeAddrs += name;
              }
            }
          }
        }
      }
      if (!storeAddrs.empty()) {
        size_t pos = boogieCode.find("1 == 1;");
        if (pos != std::string::npos) {
          boogieCode.insert(pos, "{:store_addr " + storeAddrs + "} ");
        }
      }
    }

    if (L && boogieCode.find("loop_invariant") != std::string::npos) {
      hoistLoopStmtToHeader(L, Stmt::code(boogieCode));
    } else {
      emit(Stmt::code(boogieCode));
    }

  } else if (name.find(Naming::INV_PROC_PREFIX) != StringRef::npos) {
    // Structured loop invariant intrinsics.
    // SMACK generates the full Boogie string; no format strings needed.
    // Helper: get Boogie variable name for call argument at index i
    auto bv = [&](unsigned i) -> std::string {
      std::ostringstream ss;
      rep->expr(ci.getArgOperand(i))->print(ss);
      return ss.str();
    };
    // Helper: get memory region name ($M.N) for pointer argument at index i
    auto mr = [&](unsigned i) -> std::string {
      return "$M." + std::to_string(rep->getRegions()->idx(ci.getArgOperand(i)));
    };

    std::string boogieCode;
    std::string invName = name.substr(Naming::INV_PROC_PREFIX.size()).str();

    if (invName == "byte_copy_fwd") {
      // __SMACK_inv_byte_copy_fwd(free_var, dst, src, loop_var, count)
      std::string k = bv(0), d = bv(1), s = bv(2), i = bv(3), n = bv(4);
      std::string dM = mr(1), sM = mr(2);
      boogieCode =
        "assume {:loop_invariant} {:custom \"memmove_forward_correctness\"} "
        "{:free_var " + k + "} {:d " + d + "} {:s " + s + "} "
        "{:i " + i + "} {:n " + n + "} "
        "$or.i1("
          "$not.i1($ult.i64(" + k + ", " + i + ")), "
          "$eq.i8("
            "$load.i8(" + dM + ", $add.i64(" + d + ", " + k + ")), "
            "$load.i8(" + sM + ", $add.i64(" + s + ", " + k + "))"
          ")"
        ") == 1;";

    } else if (invName == "byte_copy_bwd") {
      // __SMACK_inv_byte_copy_bwd(free_var, dst, src, loop_var, count)
      std::string k = bv(0), d = bv(1), s = bv(2), i = bv(3), n = bv(4);
      std::string dM = mr(1), sM = mr(2);
      boogieCode =
        "assume {:loop_invariant} {:custom \"memmove_backward_correctness\"} "
        "{:free_var " + k + "} {:d " + d + "} {:s " + s + "} "
        "{:i " + i + "} {:n " + n + "} "
        "$or.i1("
          "$not.i1($and.i1($ule.i64(" + i + ", " + k + "), "
                           "$ult.i64(" + k + ", " + n + "))), "
          "$eq.i8("
            "$load.i8(" + dM + ", $add.i64(" + d + ", " + k + ")), "
            "$load.i8(" + sM + ", $add.i64(" + s + ", " + k + "))"
          ")"
        ") == 1;";

    } else if (invName == "bounds") {
      // __SMACK_inv_bounds(var, upper)
      boogieCode =
        "assume {:loop_invariant} $ule.i64(" + bv(0) + ", " + bv(1) + ") == 1;";

    } else if (invName == "ptr_progress") {
      // __SMACK_inv_ptr_progress(ptr, base, total, remaining, stride)
      // stride is a compile-time constant
      std::string ptr = bv(0), base = bv(1), total = bv(2), rem = bv(3);
      std::string stride = bv(4);
      boogieCode =
        "assume {:loop_invariant} $eq.i64(" + ptr + ", "
        "$add.i64(" + base + ", $mul.i64($sub.i64(" + total + ", " + rem + "), "
        + stride + "))) == 1;";

    } else if (invName == "buffer") {
      // __SMACK_inv_buffer(ptr, ptr_init, len, len_init)
      std::string p = bv(0), pi = bv(1), l = bv(2), li = bv(3);
      boogieCode =
        "assume {:loop_invariant} {:custom \"e_buffer_consistency\"} "
        "{:free_var " + p + "} "
        "{:ptr " + p + "} {:ptr_init " + pi + "} "
        "{:len " + l + "} {:len_init " + li + "} "
        "$and.i1($ule.i64(" + l + ", " + li + "), "
        "$eq.i64(" + p + ", $add.i64(" + pi + ", $sub.i64(" + li + ", " + l + "))))"
        " == 1;";

    } else {
      llvm_unreachable(
          ("Unknown SMACK invariant intrinsic: " + name.str()).c_str());
    }

    // Hoist to loop header (same logic as __SMACK_code)
    auto L = loops[ci.getParent()];
    hoistLoopStmtToHeader(L, Stmt::code(boogieCode));

  } else if (name.find(Naming::DECL_PROC) != StringRef::npos) {
    std::string code = rep->code(ci);
    proc->getDeclarations().push_back(Decl::code(code, code));

  } else if (name.find(Naming::TOP_DECL_PROC) != StringRef::npos) {
    std::string decl = rep->code(ci);
    rep->getProgram()->getDeclarations().push_back(Decl::code(decl, decl));
    if (VAR_DECL.match(decl)) {
      std::string var = VAR_DECL.sub("\\1", decl);
      rep->addBplGlobal(var);
    }

  } else if (rep->isContractExpr(f)) {
    // NOTE do not generate code for contract expressions

  } else if (name == "__CONTRACT_int_variable") {

    // TODO assume that all variables are within an expression scope (?)
    // emit(Stmt::assign(rep->expr(&ci),
    // Expr::id(rep->getString(ci.getArgOperand(0)))));

  } else if (name == Naming::CONTRACT_FORALL) {

    llvm_unreachable("universal quantifiers not implemented.");

    // assert(ci.arg_size() == 2
    //     && "Expected contract expression argument to contract function.");
    // CallInst* cj = dyn_cast<CallInst>(ci.getArgOperand(1));
    // assert(cj && "Expected contract expression argument to contract
    // function.");
    // Function* F = cj->getCalledFunction();
    // assert(F && rep->isContractExpr(F)
    //     && "Expected contract expression argument to contract function.");
    //
    // auto binding = rep->getString(ci.getArgOperand(0));
    // std::list<const Expr*> args;
    //
    // auto AX = F->getAttributes();
    // for (unsigned i = 0; i < cj->arg_size(); i++) {
    //   std::string var = "";
    //   if (AX.hasAttribute(i+1, "contract-var"))
    //     var = AX.getAttribute(i+1, "contract-var").getValueAsString();
    //   args.push_back(
    //     var == binding ? Expr::id(binding) :
    //     rep->expr(cj->getArgOperand(i)));
    // }
    // for (auto m : rep->memoryMaps())
    //   args.push_back(Expr::id(m.first));
    // auto E = Expr::fn(F->getName(), args);
    // emit(Stmt::assign(rep->expr(&ci),
    //   Expr::ifThenElse(Expr::forall(binding, "int", E),
    //     rep->integerLit(1U,1), rep->integerLit(0U,1))));

  } else if (name == Naming::CONTRACT_REQUIRES ||
             name == Naming::CONTRACT_ENSURES ||
             name == Naming::CONTRACT_INVARIANT) {

    assert(ci.arg_size() == 1 &&
           "Expected contract expression argument to contract function.");
    CallInst *cj = dyn_cast<CallInst>(ci.getArgOperand(0));
    assert(cj && "Expected contract expression argument to contract function.");
    Function *F = cj->getCalledFunction();
    assert(F && rep->isContractExpr(F) &&
           "Expected contract expression argument to contract function.");

    std::list<const Expr *> args;
    for (auto &V : cj->args())
      args.push_back(rep->expr(V));
    for (auto m : rep->memoryMaps())
      args.push_back(Expr::id(m.first));
    auto E = Expr::fn(F->getName().str(), args);
    if (name == Naming::CONTRACT_REQUIRES)
      proc->getRequires().push_back(E);
    else if (name == Naming::CONTRACT_ENSURES)
      proc->getEnsures().push_back(E);
    else {
      auto L = loops[ci.getParent()];
      assert(L);
      auto *attr = Attr::attr(Naming::LOOP_INVARIANT_ANNOTATION);
      loopInvariants[L].push_back(E);
      hoistLoopStmtToHeader(L, Stmt::assume(E, attr));
    }

    // } else if (name == "result") {
    //   assert(ci.arg_size() == 0 && "Unexpected operands to
    //   result.");
    //   emit(Stmt::assign(rep->expr(&ci),Expr::id(Naming::RET_VAR)));
    //
    // } else if (name == "qvar") {
    //   assert(ci.arg_size() == 1 && "Unexpected operands to qvar.");
    //   emit(Stmt::assign(rep->expr(&ci),Expr::id(rep->getString(ci.getArgOperand(0)))));
    //
    // } else if (name == "old") {
    //   assert(ci.arg_size() == 1 && "Unexpected operands to old.");
    //   llvm::LoadInst* LI =
    //   llvm::dyn_cast<llvm::LoadInst>(ci.getArgOperand(0));
    //   assert(LI && "Expected value from Load.");
    //   emit(Stmt::assign(rep->expr(&ci),
    //     Expr::fn("old",rep->load(LI->getPointerOperand())) ));

    // } else if (name == "forall") {
    //   assert(ci.arg_size() == 2 && "Unexpected operands to
    //   forall.");
    //   Value* var = ci.getArgOperand(0);
    //   Value* arg = ci.getArgOperand(1);
    //   Slice* S = getSlice(arg);
    //   emit(Stmt::assign(rep->expr(&ci),
    //     Expr::forall(rep->getString(var), "int",
    //     S->getBoogieExpression(naming,rep))));
    //
    // } else if (name == "exists") {
    //   assert(ci.arg_size() == 2 && "Unexpected operands to
    //   forall.");
    //   Value* var = ci.getArgOperand(0);
    //   Value* arg = ci.getArgOperand(1);
    //   Slice* S = getSlice(arg);
    //   emit(Stmt::assign(rep->expr(&ci),
    //     Expr::exists(rep->getString(var), "int",
    //     S->getBoogieExpression(naming,rep))));
    //
    // } else if (name == "invariant") {
    //   assert(ci.arg_size() == 1 && "Unexpected operands to
    //   invariant.");
    //   Slice* S = getSlice(ci.getArgOperand(0));
    //   emit(Stmt::assert_(S->getBoogieExpression(naming,rep)));

  } else {
    emit(rep->call(f, ci));
  }

  if (f->isDeclaration()) {
    std::string name = naming->get(*f);
    if (!EXTERNAL_PROC_IGNORE.match(name) && rep->isExternal(&ci))
      emit(Stmt::assume(Expr::fn(Naming::EXTERNAL_ADDR, rep->expr(&ci))));
  }

  if ((naming->get(*f).find("__SMACK") == 0 ||
       naming->get(*f).find("__VERIFIER") == 0) &&
      !f->getReturnType()->isVoidTy()) {
    emit(recordProcedureCall(
        &ci, {Attr::attr("cexpr", "smack:ext:" + naming->get(*f))}));
  }
}

void SmackInstGenerator::visitCallBrInst(llvm::CallBrInst &cbi) {
  processInstruction(cbi);
  SmackWarnings::warnApproximate("callbr instruction " + i2s(cbi), currBlock,
                                 &cbi);
  emit(Stmt::skip());
}

bool isSourceLoc(const Stmt *stmt) {
  return (stmt->getKind() == Stmt::ASSUME &&
          (llvm::cast<const AssumeStmt>(stmt))->hasAttr("sourceloc")) ||
         (stmt->getKind() == Stmt::CALL);
}

void SmackInstGenerator::visitDbgValueInst(llvm::DbgValueInst &dvi) {
  processInstruction(dvi);

  if (SmackOptions::SourceLocSymbols) {
    Value *V = dvi.getValue();
    const llvm::DILocalVariable *var = dvi.getVariable();
    // if (V && !V->getType()->isPointerTy() && !llvm::isa<ConstantInt>(V)) {
    if (V && !V->getType()->isPointerTy()) {
      // if (currBlock->begin() != currBlock->end()
      //&& currBlock->getStatements().back()->getKind() == Stmt::ASSUME) {
      //    && isSourceLoc(currBlock->getStatements().back())) {
      // assert(&*currInst == &dvi && "Current Instruction mismatch!");
      auto currInst = std::prev(nextInst);
      if (currInst != dvi.getParent()->begin()) {
        const Instruction &pi = *std::prev(currInst);
        V = V->stripPointerCastsAndAliases();
        if (!llvm::isa<const PHINode>(&pi) &&
            V == llvm::dyn_cast<const Value>(&pi))
          emit(recordProcedureCall(
              V, {Attr::attr("cexpr", var->getName().str())}));
      }
      Function *F = dvi.getFunction();
      for (auto &arg : F->args()) {
        if (&arg == V && var->getScope() == F->getMetadata("dbg")) {
          emit(recordProcedureCall(
              V, {Attr::attr("cexpr", naming->get(*F) +
                                          ":arg:" + var->getName().str())}));
          break;
        }
      }
    }
  }
}

void SmackInstGenerator::visitLandingPadInst(llvm::LandingPadInst &lpi) {
  processInstruction(lpi);
  // TODO what exactly!?
  emit(Stmt::assign(rep->expr(&lpi), Expr::id(Naming::EXN_VAL_VAR)));
  if (lpi.isCleanup())
    emit(Stmt::assign(Expr::id(Naming::EXN_VAR), Expr::lit(false)));
  SmackWarnings::warnApproximate("landingpad clauses", currBlock, &lpi);
}

/******************************************************************************/
/*                  INTRINSIC                    FUNCTIONS                    */
/******************************************************************************/

void SmackInstGenerator::visitMemCpyInst(llvm::MemCpyInst &mci) {
  processInstruction(mci);
  emit(rep->memcpy(mci));
}

void SmackInstGenerator::visitMemSetInst(llvm::MemSetInst &msi) {
  processInstruction(msi);
  emit(rep->memset(msi));
}

void SmackInstGenerator::visitIntrinsicInst(llvm::IntrinsicInst &ii) {
  processInstruction(ii);

  //(CallInst -> Void) -> [Flags] -> (CallInst -> Void)
  static const auto conditionalModel =
      [this](std::function<void(CallInst *)> modelGenFunc,
             std::initializer_list<const cl::opt<bool> *> requiredFlags,
             SmackWarnings::FlagRelation rel =
                 SmackWarnings::FlagRelation::And) {
        auto unsetFlags = SmackWarnings::getUnsetFlags(requiredFlags);
        auto satisfied = SmackWarnings::isSatisfied(requiredFlags, rel);
        return [this, unsetFlags, modelGenFunc, satisfied, rel](CallInst *ci) {
          if (satisfied)
            modelGenFunc(ci);
          else {
            SmackWarnings::warnOverApproximate(
                "call to " + ci->getCalledFunction()->getName().str(),
                unsetFlags, currBlock, ci, rel);
            emit(rep->call(ci->getCalledFunction(), *ci));
          }
        };
      };

  // Optionally generate a boogie assume statement from assume statements in
  // LLVM. Currently this behavior is experimental and must be enabled by
  // passing the -llvm-assumes flag. The default behavior of this
  // function is to ignore the assume statement, specified by the "none"
  // argument. If the check argument is given, an additional assertion is
  // generated to check the validity of the assumption.
  static const auto assume = [this](CallInst *ci) {
    if (SmackOptions::LLVMAssumes != LLVMAssumeType::none) {
      auto arg = rep->expr(ci->getArgOperand(0));
      auto llvmTrue =
          SmackOptions::BitPrecise ? Expr::lit(1, 1) : Expr::lit(1LL);
      auto chkStmt = Expr::eq(arg, llvmTrue);
      if (SmackOptions::LLVMAssumes == LLVMAssumeType::check &&
          SmackOptions::shouldCheckFunction(ci->getFunction()->getName()))
        emit(Stmt::assert_(chkStmt));
      else
        emit(Stmt::assume(chkStmt));
    } else {
      // Skip assume statements
      return;
    }
  };

  static const auto f16UpCast = conditionalModel(
      [this](CallInst *ci) {
        // translation: $f := $fpext.bvhalf.*($rmode, $bitcast.bv16.bvhalf($i));
        auto argT = rep->type(ci->getArgOperand(0)->getType());
        auto retT = rep->type(ci->getFunctionType()->getReturnType());
        emit(Stmt::assign(
            rep->expr(ci),
            Expr::fn(
                indexedName("$fpext", {Naming::HALF_TYPE, retT}),
                {Expr::id(Naming::RMODE_VAR),
                 Expr::fn(indexedName("$bitcast", {argT, Naming::HALF_TYPE}),
                          rep->expr(ci->getArgOperand(0)))})));
      },
      {&SmackOptions::FloatEnabled, &SmackOptions::BitPrecise});

  static const auto f16DownCast = conditionalModel(
      [this](CallInst *ci) {
        // translation: assume($bitcast.bv16.bvhalf($i) ==
        // $fptrunc.bvfloat.bvhalf($rmode, $f));
        auto argT = rep->type(ci->getArgOperand(0)->getType());
        auto retT = rep->type(ci->getFunctionType()->getReturnType());
        emit(Stmt::assume(Expr::eq(
            Expr::fn(indexedName("$fptrunc", {argT, Naming::HALF_TYPE}),
                     Expr::id(Naming::RMODE_VAR),
                     rep->expr(ci->getArgOperand(0))),
            Expr::fn(indexedName("$bitcast", {retT, Naming::HALF_TYPE}),
                     rep->expr(ci)))));
      },
      {&SmackOptions::FloatEnabled, &SmackOptions::BitPrecise});

  static const auto fma = conditionalModel(
      [this](CallInst *ci) {
        emit(Stmt::assign(
            rep->expr(ci),
            Expr::fn(indexedName(
                         "$fma",
                         {rep->type(ci->getFunctionType()->getReturnType())}),
                     rep->expr(ci->getArgOperand(0)),
                     rep->expr(ci->getArgOperand(1)),
                     rep->expr(ci->getArgOperand(2)))));
      },
      {&SmackOptions::FloatEnabled});

  static const auto bitreverse = [this](Value *arg) {
    auto width = arg->getType()->getIntegerBitWidth();
    auto var = rep->expr(arg);

    // Swap the bits to the right and left of the middle
    const Expr *body;
    if (width % 2 == 0) {
      body = Expr::bvConcat(Expr::bvExtract(var, width / 2, width / 2 - 1),
                            Expr::bvExtract(var, width / 2 + 1, width / 2));
    } else {
      body = Expr::bvExtract(var, width / 2 + 1, width / 2);
    }
    // Swap the bits to the right and the left of the already swapped portion.
    unsigned offset = width & 1;
    for (unsigned i = width % 2 == 0 ? 1 : 0; i < width / 2; ++i) {
      body = Expr::bvConcat(
          Expr::bvConcat(Expr::bvExtract(var, width / 2 - i, width / 2 - i - 1),
                         body),
          Expr::bvExtract(var, width / 2 + i + 1 + offset,
                          width / 2 + i + offset));
    }
    return body;
  };

  static const auto bswap = [this](Value *arg) {
    auto width = arg->getType()->getIntegerBitWidth();
    auto var = rep->expr(arg);

    // Swap the bytes to the right and left of the middle
    const Expr *body =
        Expr::bvConcat(Expr::bvExtract(var, width / 2, width / 2 - 8),
                       Expr::bvExtract(var, width / 2 + 8, width / 2));

    // Swap the bytes to the right and the left of the already swapped portion.
    for (unsigned i = 8; i < width / 2; i += 8) {
      body = Expr::bvConcat(
          Expr::bvConcat(Expr::bvExtract(var, width / 2 - i, width / 2 - i - 8),
                         body),
          Expr::bvExtract(var, width / 2 + i + 8, width / 2 + i));
    }
    return body;
  };

  // Count leading zeros
  static const auto ctlz = conditionalModel(
      [this](CallInst *ci) {
        auto width = ci->getArgOperand(0)->getType()->getIntegerBitWidth();
        auto var = rep->expr(ci->getArgOperand(0));

        // e.g., if v[32:31] == 1 then 0bv32 else if v[31:30] == 1 then 1bv32
        // else
        // ... else if v[1:0] == 1 then 31bv32 else 32bv32
        const Expr *body = Expr::lit(width, width);
        for (unsigned i = 0; i < width; ++i) {
          body = Expr::ifThenElse(
              Expr::eq(Expr::bvExtract(var, i + 1, i), Expr::lit(1, 1)),
              Expr::lit(width - i - 1, width), body);
        }

        // Handle the is_zero_undef case, i.e. if the flag is set and the
        // argument
        // is zero, then the result is undefined.
        auto isZeroUndef = rep->expr(ci->getArgOperand(1));
        body =
            Expr::ifThenElse(Expr::and_(Expr::eq(isZeroUndef, Expr::lit(1, 1)),
                                        Expr::eq(var, Expr::lit(0, width))),
                             rep->expr(ci), // The result is undefined
                             body);
        emit(Stmt::havoc(rep->expr(ci)));
        emit(Stmt::assign(rep->expr(ci), body));
      },
      {&SmackOptions::BitPrecise});

  // Count trailing zeros
  static const auto cttz = conditionalModel(
      [this](CallInst *ci) {
        auto width = ci->getArgOperand(0)->getType()->getIntegerBitWidth();
        auto arg = rep->expr(ci->getArgOperand(0));

        // e.g., if v[1:0] == 1 then 0bv32 else if v[2:1] == 1 then 1bv32 else
        // ... else if v[32:31] == 1 then 31bv32 else 32bv32
        const Expr *body = Expr::lit(width, width);
        for (unsigned i = width; i > 0; --i) {
          body = Expr::ifThenElse(
              Expr::eq(Expr::bvExtract(arg, i, i - 1), Expr::lit(1, 1)),
              Expr::lit(i - 1, width), body);
        }

        // Handle the is_zero_undef case, i.e. if the flag is set and the
        // argument
        // is zero, then the result is undefined.
        auto isZeroUndef = rep->expr(ci->getArgOperand(1));
        body =
            Expr::ifThenElse(Expr::and_(Expr::eq(isZeroUndef, Expr::lit(1, 1)),
                                        Expr::eq(arg, Expr::lit(0, width))),
                             rep->expr(ci), // The result is undefined
                             body);
        emit(Stmt::havoc(rep->expr(ci)));
        emit(Stmt::assign(rep->expr(ci), body));
      },
      {&SmackOptions::BitPrecise});

  // Count the population of 1s in a bv
  static const auto ctpop = conditionalModel(
      [this](CallInst *ci) {
        Value *arg = ci->getArgOperand(0);
        auto width = arg->getType()->getIntegerBitWidth();
        auto var = rep->expr(arg);
        const Expr *body = nullptr;
        auto type = rep->type(arg->getType());

        if (SmackOptions::BitPrecise) { // Bitvector mode
          body = Expr::lit(0, width);
          for (unsigned i = 0; i < width; ++i) {
            body = Expr::fn(indexedName("$add", {type}),
                            Expr::fn(indexedName("$zext", {"bv1", type}),
                                     Expr::bvExtract(var, i + 1, i)),
                            body);
          }
        } else { // Otherwise, try with the integer encoding
          body = Expr::lit(0ull);
          for (unsigned i = 0; i < width; ++i) {
            auto quotient =
                Expr::fn(indexedName("$udiv", {type}), var,
                         Expr::lit((unsigned long long)(1ull << i)));
            auto remainder = Expr::fn(indexedName("$urem", {type}), quotient,
                                      Expr::lit(2ull));
            body = Expr::fn(indexedName("$add", {type}), remainder, body);
          }
        }
        emit(Stmt::assign(rep->expr(ci), body));
      },
      {&SmackOptions::BitPrecise, &SmackOptions::RewriteBitwiseOps},
      SmackWarnings::FlagRelation::Or);

  static const auto assignBvExpr =
      [this](std::function<const Expr *(Value *)> exprGenFunc) {
        return conditionalModel(
            [this, exprGenFunc](CallInst *ci) {
              emit(Stmt::assign(rep->expr(ci),
                                exprGenFunc(ci->getArgOperand(0))));
            },
            {&SmackOptions::BitPrecise});
      };

  static const auto assignUnFPFuncApp = [this](std::string fnBase) {
    return conditionalModel(
        [this, fnBase](CallInst *ci) {
          // translation: $res := $<func>.bv*($arg1);
          emit(Stmt::assign(
              rep->expr(ci),
              Expr::fn(
                  indexedName(fnBase,
                              {rep->type(ci->getArgOperand(0)->getType())}),
                  rep->expr(ci->getArgOperand(0)))));
        },
        {&SmackOptions::FloatEnabled});
  };

  static const auto assignBinFPFuncApp = [this](std::string fnBase) {
    return conditionalModel(
        [this, fnBase](CallInst *ci) {
          // translation: $res := $<func>.bv*($arg1, $arg2);
          emit(Stmt::assign(
              rep->expr(ci),
              Expr::fn(indexedName(
                           fnBase,
                           {rep->type(ci->getFunctionType()->getReturnType())}),
                       {rep->expr(ci->getArgOperand(0)),
                        rep->expr(ci->getArgOperand(1))})));
        },
        {&SmackOptions::FloatEnabled});
  };

  // Expr* -> (CallInst -> Void)
  static const auto assignRoundFPFuncApp = [this](const Expr *rMode) {
    return conditionalModel(
        [this, rMode](CallInst *ci) {
          emit(Stmt::assign(
              rep->expr(ci),
              Expr::fn(indexedName(
                           "$round",
                           {rep->type(ci->getFunctionType()->getReturnType())}),
                       {rMode, rep->expr(ci->getArgOperand(0))})));
        },
        {&SmackOptions::FloatEnabled});
  };

  static const auto isFpClass = conditionalModel(
      [this](CallInst *ci) {
        auto *arg = ci->getArgOperand(0);
        auto *maskConst = dyn_cast<ConstantInt>(ci->getArgOperand(1));
        if (!maskConst) {
          SmackWarnings::warnApproximate(
              ci->getCalledFunction()->getName().str(), currBlock, ci);
          emit(rep->call(ci->getCalledFunction(), *ci));
          return;
        }

        auto mask = maskConst->getZExtValue();
        auto type = rep->type(arg->getType());
        auto value = rep->expr(arg);
        auto boolPred = [type, value](std::string name) {
          return Expr::fn(indexedName(name, {type, Naming::BOOL_TYPE}), value);
        };
        auto signedPred = [&](const Expr *classPred, bool negative) {
          auto sign = boolPred(negative ? "$isnegative" : "$ispositive");
          return Expr::and_(classPred, sign);
        };

        const Expr *pred = Expr::lit(false);
        auto add = [&](bool include, const Expr *classPred) {
          if (include)
            pred = Expr::or_(pred, classPred);
        };
        auto addSignedClass = [&](uint64_t negMask, uint64_t posMask,
                                  std::string className) {
          bool neg = (mask & negMask) != 0;
          bool pos = (mask & posMask) != 0;
          auto classPred = boolPred(className);
          if (neg && pos)
            add(true, classPred);
          else if (neg)
            add(true, signedPred(classPred, true));
          else if (pos)
            add(true, signedPred(classPred, false));
        };

        if ((mask & llvm::fcNan) == llvm::fcNan)
          add(true, boolPred("$isnan"));
        else if (mask & llvm::fcNan) {
          SmackWarnings::warnApproximate("llvm.is.fpclass nan subclass",
                                         currBlock, ci);
          add(true, boolPred("$isnan"));
        }

        addSignedClass(llvm::fcNegInf, llvm::fcPosInf, "$isinfinite");
        addSignedClass(llvm::fcNegNormal, llvm::fcPosNormal, "$isnormal");
        addSignedClass(llvm::fcNegSubnormal, llvm::fcPosSubnormal,
                       "$issubnormal");
        addSignedClass(llvm::fcNegZero, llvm::fcPosZero, "$iszero");

        emit(Stmt::assign(rep->expr(ci),
                          Expr::ifThenElse(pred, rep->integerLit(1ULL, 1),
                                           rep->integerLit(0ULL, 1))));
      },
      {&SmackOptions::FloatEnabled});

  static const auto identity = [this](CallInst *ci) {
    // translation: $res := $arg1
    Value *val = ci->getArgOperand(0);
    emit(Stmt::assign(rep->expr(ci), rep->expr(val)));
  };

  static const auto ignore = [this](CallInst *ci) { emit(Stmt::skip()); };

  // TODO: these functions is consistent with the implementations in math.c,
  // meaning we can use __builtin_* to implement math.c which is mostly
  // modeled using __SMACK_code.

  static const std::map<llvm::Intrinsic::ID, std::function<void(CallInst *)>>
      stmtMap{
          {llvm::Intrinsic::assume, assume},
          {llvm::Intrinsic::bitreverse, assignBvExpr(bitreverse)},
          {llvm::Intrinsic::bswap, assignBvExpr(bswap)},
          {llvm::Intrinsic::convert_from_fp16, f16UpCast},
          {llvm::Intrinsic::convert_to_fp16, f16DownCast},
          {llvm::Intrinsic::ctlz, ctlz},
          {llvm::Intrinsic::ctpop, ctpop},
          {llvm::Intrinsic::cttz, cttz},
          {llvm::Intrinsic::dbg_declare, ignore},
          {llvm::Intrinsic::dbg_label, ignore},
          {llvm::Intrinsic::expect, identity},
          {llvm::Intrinsic::fabs, assignUnFPFuncApp("$abs")},
          {llvm::Intrinsic::fma, fma},
          {llvm::Intrinsic::is_fpclass, isFpClass},
          {llvm::Intrinsic::sqrt, assignUnFPFuncApp("$sqrt")},
          {llvm::Intrinsic::maxnum, assignBinFPFuncApp("$max")},
          {llvm::Intrinsic::minnum, assignBinFPFuncApp("$min")},
          {llvm::Intrinsic::ceil,
           assignRoundFPFuncApp(Expr::lit(RModeKind::RTP))},
          {llvm::Intrinsic::floor,
           assignRoundFPFuncApp(Expr::lit(RModeKind::RTN))},
          {llvm::Intrinsic::nearbyint,
           assignRoundFPFuncApp(Expr::id(Naming::RMODE_VAR))},
          {llvm::Intrinsic::rint,
           assignRoundFPFuncApp(Expr::id(Naming::RMODE_VAR))},
          {llvm::Intrinsic::round,
           assignRoundFPFuncApp(Expr::lit(RModeKind::RNA))},
          {llvm::Intrinsic::trunc,
           assignRoundFPFuncApp(Expr::lit(RModeKind::RTZ))}
          // TODO: we cannot properly handle copysign because our fp2bv is not
          // carefully implemented.
          // The current version of llvm does not have these intrinsics while
          // the latest version does
          // we keep the code to save work in the future
          // TODO: in future versions, there may be intrinsics that round floats
          // to integers like lround
      };

  auto it = stmtMap.find(ii.getIntrinsicID());
  if (it != stmtMap.end())
    it->second(&ii);
  else if (ii.getIntrinsicID() ==
           llvm::Intrinsic::experimental_noalias_scope_decl) {
    // Ignore this function as we cannot handle arguments of metadata type.
  } else {
    SmackWarnings::warnApproximate(ii.getCalledFunction()->getName().str(),
                                   currBlock, &ii);
    emit(rep->call(ii.getCalledFunction(), ii));
  }
}

} // namespace smack
