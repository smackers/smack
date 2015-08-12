//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/Region.h"

namespace smack {

void Region::unifyWith(const llvm::DSNode* node, unsigned long offset, unsigned long size, bool a, bool m, bool i) {
  lowOffset = lowOffset < offset ? lowOffset : offset;
  unsigned long ho = offset + size - 1;
  highOffset = highOffset > ho ? highOffset : ho;
  allocated = allocated || a;
  memcpyd = memcpyd || m;
  staticInitd = staticInitd || i;
}

void Region::unifyWith(Region r) {
  assert(singletonGlobal == r.singletonGlobal);
  lowOffset = lowOffset < r.lowOffset ? lowOffset : r.lowOffset;
  highOffset = highOffset > r.highOffset ? highOffset : r.highOffset;
  allocated = allocated || r.allocated;
  memcpyd = memcpyd || r.memcpyd;
  staticInitd = staticInitd || r.staticInitd;
}

} // namespace smack
