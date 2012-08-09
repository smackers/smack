//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef MEMORY_H_
#define MEMORY_H_

#include "Common.h"
#include "llvm/Support/Debug.h"
#include <assert.h>
#include <ostream>
#include <sstream>
#include <string>

namespace smack {

class Memory {
private:
  Memory() {}
  
public:
  static Memory* create();
  void print(std::ostream &os) const;
};
std::ostream &operator<<(std::ostream &os, const Memory* mem);
std::ostream &operator<<(std::ostream &os, const Memory& mem);

}

#endif /*MEMORY_H_*/
