//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/RegionManager.h"
// #define DEBUG_TYPE "region-manager"

namespace smack {

unsigned RegionManager::size() {
  return memoryRegions.size();
}

Region RegionManager::getRegion(unsigned idx) {
  return memoryRegions[idx];
}

unsigned RegionManager::getRegion(const llvm::Value* v) {
  // DEBUG(errs() << "YYY - getRegion(" << *v << ")\n");

  if (SmackOptions::NoMemoryRegionSplitting) {
    llvm::Type* T = v->getType();
    while (T->isPointerTy()) T = T->getPointerElementType();
    if (memoryRegions.empty())
      memoryRegions.emplace_back(nullptr, 0, ULONG_MAX, aliasAnalysis && aliasAnalysis->isAlloced(v));
    else
      memoryRegions[0] = Region(nullptr, 0, ULONG_MAX,
          memoryRegions[0].isAllocated() || (aliasAnalysis && aliasAnalysis->isAlloced(v)));
    return 0;
  } else {
    unsigned firstMR = UINT_MAX;
    unsigned mr;

    for (mr=0; mr<memoryRegions.size(); ++mr) {
      Region r = memoryRegions[mr];
      AliasAnalysis::AliasResult aliasResult = aliasAnalysis->alias(r, v);
      if (aliasResult != AliasAnalysis::NoAlias) {
        if (firstMR == UINT_MAX) {
          firstMR = mr;
          const DSNode* node = aliasAnalysis->getNode(v);
          memoryRegions[firstMR].unifyWith(node, aliasAnalysis->getOffset(v), aliasAnalysis->getPointedTypeSize(v),
              aliasAnalysis->isAlloced(v), aliasAnalysis->isMemcpyd(node), aliasAnalysis->isStaticInitd(node));
        } else {
          memoryRegions[firstMR].unifyWith(r);
          memoryRegions.erase(memoryRegions.begin() + mr);
        }
      }
    }

    if (firstMR == UINT_MAX) {
      firstMR = mr;
      llvm::Type* T = v->getType();
      while (T->isPointerTy()) T = T->getPointerElementType();
      unsigned long offset = aliasAnalysis->getOffset(v);
      memoryRegions.emplace_back(aliasAnalysis->getNode(v), offset, offset + aliasAnalysis->getPointedTypeSize(v),
          aliasAnalysis->isAlloced(v),
          aliasAnalysis->isSingletonGlobal(v) && T->isSingleValueType(),
          aliasAnalysis->isMemcpyd(aliasAnalysis->getNode(v)),
          aliasAnalysis->isStaticInitd(aliasAnalysis->getNode(v))
      );
    }

    // DEBUG(errs() << "YYY - getRegion(" << *v << ") => " << firstMR << "\n");
    return firstMR;
  }
}

} // namespace smack
