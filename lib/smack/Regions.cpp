//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/Regions.h"

namespace smack {

unsigned RegionManager::size() {
  return memoryRegions.size();
}

Region RegionManager::getRegion(unsigned idx) {
  return memoryRegions[idx];
}

unsigned RegionManager::getRegion(const llvm::Value* v) {
  unsigned mr;
  unsigned firstMR = UINT_MAX;
  set<const llvm::Value*>::iterator r;

  if (SmackOptions::NoMemoryRegionSplitting)
    mr = 0;
  else
    for (mr=0; mr<memoryRegions.size(); ++mr) {
      for (r = memoryRegions[mr].representatives.begin(); r != memoryRegions[mr].representatives.end(); ++r) {
        if (llvm::PointerType* vType = llvm::dyn_cast<llvm::PointerType>(v->getType()))
          if (llvm::PointerType* rType = llvm::dyn_cast<llvm::PointerType>((*r)->getType())) {
            llvm::Type* vPointedType = vType->getTypeAtIndex(0u);
            llvm::Type* rPointedType = rType->getTypeAtIndex(0u);

            if (vPointedType->isSized() && rPointedType->isSized()) {
              uint64_t vSize = targetData->getTypeStoreSize(vPointedType);
              uint64_t rSize = targetData->getTypeStoreSize(rPointedType);
              if (!aliasAnalysis->isNoAlias(v, vSize, *r, rSize))
                break;
            } else
              if (!aliasAnalysis->isNoAlias(v, *r))
                break;
          } else
            assert(false && "Region type should be pointer.");
        else
          assert(false && "Region type should be pointer.");
      }
      if (r != memoryRegions[mr].representatives.end()) {
        if (firstMR == UINT_MAX) {
          firstMR = mr;
          memoryRegions[firstMR].representatives.insert(v);
        } else {
          memoryRegions[firstMR].unifyWith(memoryRegions[mr]);
          memoryRegions.erase(memoryRegions.begin() + mr);
        }
      }
    }

  if (firstMR == UINT_MAX) {
    firstMR = mr;
    llvm::Type* T = v->getType();
    while (T->isPointerTy()) T = T->getPointerElementType();
    memoryRegions.emplace_back(v,false,
      aliasAnalysis && aliasAnalysis->isSingletonGlobal(v) && T->isSingleValueType()
    );
  }

  memoryRegions[firstMR].isAllocated = memoryRegions[firstMR].isAllocated ||
    (aliasAnalysis && aliasAnalysis->isAlloced(v));
  return firstMR;
}

} // namespace smack
