//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef COMMON_H_
#define COMMON_H_

#include <string>

namespace smack {


struct Common {
  const static std::string MAIN_PROCEDURE;
  
  const static std::string ASSERT;
  const static std::string ASSUME;

  static unsigned INT_WIDTH;
  static std::string int_const(uint64_t i);
};

}

#endif /*COMMON_H_*/
