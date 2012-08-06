//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Memory.h"

using namespace smack;

namespace smack {

std::ostream &operator<<(std::ostream &os, const Memory* mem) {
  if (mem == 0) {
    os << "<null> Memory!\n";
  } else {
    mem->print(os);
  }
  return os;
}
 
std::ostream &operator<<(std::ostream &os, const Memory& mem) {
  mem.print(os);
  return os;
}
}

Memory* Memory::create() {
  Memory* mem = new Memory();
  return mem;
}

void Memory::print(std::ostream &os) const {
  os << "Mem";
}
