//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Utils.h"
#include "llvm/Support/Regex.h"

using namespace smack;
using namespace std;
using namespace llvm;

namespace smack {

  string EscapeString(string str) {
    str = llvm::DOT::EscapeString(str);
    return str;
  }
  
  Regex BPL_KW(
    "bool|int|false|true|old|forall|exists|requires|modifies|ensures|invariant"
    "|free|unique|finite|complete|type|const|function|axiom|var|procedure"
    "|implementation|where|returns|assume|assert|havoc|call|return|while"
    "|break|goto|if|else" );
  Regex SMACK_NAME(".*__SMACK_.*");
  Regex CPP_NAMETX("(_ZN?[0-9]*)([A-Za-z0-9_$#@!?]+)(i|pv)");
  
  string strip(string s) {
    SmallVector<StringRef,4> matches;
    if (CPP_NAMETX.match(s,&matches))
      return matches[2];
    else
      return s;
  }
  
  bool isBplKeyword(string s) {
    return BPL_KW.match(s);
  }
  
  bool isSmackProc(string s) {
    return SMACK_NAME.match(s);
  }
}
