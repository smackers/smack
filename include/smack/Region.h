//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef REGION_H
#define REGION_H

#include "dsa/DSGraph.h"

namespace smack {

using namespace std;

class Region {
private:
  const llvm::DSNode* representative;
  unsigned long lowOffset;
  unsigned long highOffset;
  bool allocated;
  bool singletonGlobal;
  bool memcpyd;
  bool staticInitd;

public:
  Region(const llvm::DSNode* r, unsigned long lo, unsigned long ho, bool a, bool s = false, bool m = false, bool i = false) :
    representative(r), lowOffset(lo), highOffset(ho), allocated(a), singletonGlobal(s), memcpyd(m), staticInitd(i) {}
  void unifyWith(const llvm::DSNode* node, unsigned long offset, unsigned long size, bool a, bool m, bool i);
  void unifyWith(Region r);

  unsigned long getHighOffset() const {
    return highOffset;
  }

  bool isAllocated() const {
    return allocated;
  }

  unsigned long getLowOffset() const {
    return lowOffset;
  }

  const llvm::DSNode* getRepresentative() const {
    return representative;
  }

  bool isSingletonGlobal() const {
    return singletonGlobal;
  }

  bool isMemcpyd() const {
    return memcpyd;
  }

  bool isStaticInitd() const {
    return staticInitd;
  }
};

}

#endif // REGION_H
