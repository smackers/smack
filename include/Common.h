//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef COMMON_H_
#define COMMON_H_

#include <string>
#include "llvm/Constants.h"
#include "llvm/Instructions.h"
#include "llvm/Support/Debug.h"

namespace smack {


struct Common {
  const static std::string MAIN_PROCEDURE;
  
  const static std::string ASSERT;
  const static std::string ASSUME;

  static unsigned INT_WIDTH;
  static std::string int_const(int64_t i);
  static std::string int_const(const llvm::APInt &ap);
};

}

#endif /*COMMON_H_*/
