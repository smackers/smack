//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Common.h"
#include <sstream>

using namespace smack;
using namespace std;

const string Common::MAIN_PROCEDURE = "main";

const string Common::ASSERT = "__SMACK_assert";
const string Common::ASSUME = "__SMACK_assume";

unsigned Common::INT_WIDTH = 0;

string Common::int_const(int64_t i) {
  stringstream s;
  if (INT_WIDTH == 0)
    s << i;
  else
    s << i << "bv" << INT_WIDTH;
  return s.str();
}

string Common::int_const(const llvm::APInt &ap) {
  stringstream s;
  
  if (INT_WIDTH == 0)
    s << ap.toString(10,true);
  
  else if (ap.isNegative())
    s << "$sub(0bv" << INT_WIDTH << "," 
      << ap.toString(10,true).substr(1) << "bv" << INT_WIDTH << ")";
    
  else
    s << ap.toString(10,true) << "bv" << INT_WIDTH;
  
  return s.str();
}
