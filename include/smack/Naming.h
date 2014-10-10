//
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef NAMING_H
#define NAMING_H

#include "llvm/Support/Regex.h"
#include "llvm/IR/Value.h"
#include <stack>
#include <map>

namespace smack {

using namespace std;
using llvm::Regex;
using llvm::Value;

class Naming {
  static Regex BPL_KW;
  static Regex SMACK_NAME;

  typedef map<const Value*, string> NameMap;
  stack<NameMap> nameStack;
  unsigned blockNum;
  unsigned varNum;

public:
  static const string BLOCK_LBL;
  static const string RET_VAR;
  static const string EXN_VAR;
  static const string EXN_VAL_VAR;
  static const string BOOL_VAR;
  static const string FLOAT_VAR;
  static const string PTR_VAR;
  static const string UNDEF_SYM;

  Naming() : blockNum(0), varNum(0) { }
  void enter();
  void leave();
  string get(const Value& V);
  string freshBlockName();
  string freshVarName(const Value& V);

  static bool isBplKeyword(string s);
  static bool isSmackName(string s);
  static bool isSmackGeneratedName(string s);
  static string escape(string s);
};

}

#endif
