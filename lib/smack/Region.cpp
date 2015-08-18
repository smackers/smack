//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/Region.h"

namespace smack {

Region::Region(const llvm::Value* V, DSAAliasAnalysis* AA) {
  if (AA) {
    llvm::Type* T = V->getType();
    while (T->isPointerTy()) T = T->getPointerElementType();
    representative = AA->getNode(V);
    offset = AA->getOffset(V);
    length = AA->getPointedTypeSize(V);
    allocated = AA->isAlloced(V);
    singleton = AA->isSingletonGlobal(V) && T->isSingleValueType();
    memcpyd = AA->isMemcpyd(representative);
    staticInitd = AA->isStaticInitd(representative);
  } else {
    representative = nullptr;
    offset = 0;
    length = std::numeric_limits<unsigned long>::max();
    allocated = false;
    singleton = false;
    memcpyd = false;
    staticInitd = false;
  }
}

void Region::merge(Region& R) {
  assert(singleton == R.singleton);
  unsigned long low = std::min(offset, R.offset);
  unsigned long high = std::max(offset + length, R.offset + R.length);
  offset = low;
  length = high - low;
  allocated = allocated || R.allocated;
  memcpyd = memcpyd || R.memcpyd;
  staticInitd = staticInitd || R.staticInitd;
}

bool Region::overlaps(Region& R) {
  return (isIncomplete() && R.isIncomplete())
      || (isComplicated() && R.isComplicated())
      || (representative == R.representative
          && !isDisjoint(R.offset, R.length));
}

} // namespace smack
