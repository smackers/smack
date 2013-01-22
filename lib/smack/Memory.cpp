//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Memory.h"

using namespace smack;
using namespace std;

namespace smack {

ostream &operator<<(ostream &os, const Memory* mem) {
  if (mem == 0) {
    os << "<null> Memory!" << endl;
  } else {
    mem->print(os);
  }
  return os;
}
 
ostream &operator<<(ostream &os, const Memory& mem) {
  mem.print(os);
  return os;
}
}

Memory* Memory::create() {
  Memory* mem = new Memory();
  return mem;
}

void Memory::print(ostream &os) const {
  os << "$Mem";
}
