//
// This file is distributed under the MIT License. See LICENSE for details.
//

//
// This pass normalizes loop structures to allow easier generation of Boogie
// code when a loop edge comes from a branch. Specifically, a forwarding block
// is added between a branching block and the loop header.
//

#include "smack/NormalizeLoops.h"
#include "smack/Naming.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ValueSymbolTable.h"
#include <map>
#include <set>
#include <vector>

namespace smack {

using namespace llvm;

// Register LoopInfo
void NormalizeLoops::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<LoopInfoWrapperPass>();
}

/**
 * Creates a basic block which unconditionally branches to \param target.
 */
BasicBlock *makeForwardingBlock(BasicBlock *target) {
  auto &context = target->getContext();
  BasicBlock *result =
      BasicBlock::Create(context, "forwarder", target->getParent());
  BranchInst *branch = BranchInst::Create(target);
  result->getInstList().push_back(branch);
  return result;
}

/**
 * Returns a vector of each successor index in \param ti which equals \param
 * headerBlock.
 */
std::vector<unsigned> getSuccessorIndices(Instruction *ti,
                                          BasicBlock *headerBlock) {
  std::vector<unsigned> result;
  unsigned numSuccs = ti->getNumSuccessors();

  if (numSuccs <= 1) {
    return result;
  }

  for (unsigned i = 0; i < numSuccs; ++i) {
    if (ti->getSuccessor(i) == headerBlock) {
      result.push_back(i);
    }
  }
  return result;
}

/**
 * Splits any edge between \param BB and \param headerBlock in a loop body,
 * by adding a forwarding block between \param BB and \param headerBlock. The
 * \param blockMap is updated to map between \param BB and the newly created
 * forwarding block.
 */
void splitBlock(BasicBlock *BB, BasicBlock *headerBlock,
                std::map<BasicBlock *, BasicBlock *> &blockMap) {
  Instruction *ti = BB->getTerminator();

  // Get a list of all successor indices which point to headerBlock.
  std::vector<unsigned> succIndices = getSuccessorIndices(ti, headerBlock);

  // TerminatorInsts may have the header block listed multiple times as a
  // successor block, e.g., in a SwitchInst. We need to make sure each such
  // index uses the same forwarding block.
  if (succIndices.size()) {
    BasicBlock *forwarder = makeForwardingBlock(headerBlock);
    blockMap[BB] = forwarder;
    for (auto succIndex : succIndices) {
      ti->setSuccessor(succIndex, forwarder);
    }
  }
}

/**
 * \param blockMap a map from old BasicBlocks and new BasicBlocks.
 * Fixes any PHI nodes in \param phis to get their incoming block from the new
 * blocks in \param blockMap.
 */
void processPhis(std::vector<PHINode *> &phis,
                 std::map<BasicBlock *, BasicBlock *> &blockMap) {
  for (PHINode *phi : phis) {
    unsigned numIncoming = phi->getNumIncomingValues();
    for (unsigned i = 0; i < numIncoming; ++i) {
      BasicBlock *incomingBlock = phi->getIncomingBlock(i);
      if (blockMap.count(incomingBlock)) {
        phi->setIncomingBlock(i, blockMap[incomingBlock]);
      }
    }
  }
}

void processLoop(Loop *loop) {
  std::vector<PHINode *> phis;
  std::set<BasicBlock *> phiIncBlocks;
  std::set<BasicBlock *> loopBlocks(loop->block_begin(), loop->block_end());
  BasicBlock *headerBlock = loop->getHeader();

  // Gather Phis in the header
  for (Instruction &I : *headerBlock) {
    if (auto *phi = dyn_cast<PHINode>(&I)) {
      phis.push_back(phi);
      phiIncBlocks.insert(phi->block_begin(), phi->block_end());
    }
  }

  std::map<BasicBlock *, BasicBlock *> blockMap;

  // Add forwarding blocks
  for (BasicBlock *BB : phiIncBlocks) {
    if (loopBlocks.count(BB) == 0) {
      continue;
    }
    splitBlock(BB, headerBlock, blockMap);
  }

  // Fix up Phi nodes
  processPhis(phis, blockMap);

  // Handle subloops
  for (Loop *subloop : loop->getSubLoops()) {
    processLoop(subloop);
  }
}

bool NormalizeLoops::runOnModule(Module &m) {
  for (auto F = m.begin(), FEnd = m.end(); F != FEnd; ++F) {
    if (F->isIntrinsic() || F->empty()) {
      continue;
    }
    LoopInfo &loopInfo = getAnalysis<LoopInfoWrapperPass>(*F).getLoopInfo();
    for (LoopInfo::iterator LI = loopInfo.begin(), LIEnd = loopInfo.end();
         LI != LIEnd; ++LI) {
      processLoop(*LI);
    }
  }

  return true;
}

// Pass ID variable
char NormalizeLoops::ID = 0;

StringRef NormalizeLoops::getPassName() const { return "NormalizeLoops"; }
} // namespace smack
