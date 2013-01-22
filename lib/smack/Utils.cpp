//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "Utils.h"

#ifdef __APPLE__
  #include <regex>
#else
  #include <tr1/regex>
#endif

using namespace smack;
using namespace std;

namespace smack {

  string EscapeString(string str) {
    str = llvm::DOT::EscapeString(str);
    return str;
  }
  
  regex BPLKW(
    "bool|int|false|true|old|forall|exists|requires|modifies|ensures|invariant"
    "|free|unique|finite|complete|type|const|function|axiom|var|procedure"
    "|implementation|where|returns|assume|assert|havoc|call|return|while"
    "|break|goto|if|else" );
  
  regex SMACKKW(".*__SMACK_.*");
  regex RRR("(_ZN?[0-9]*)([A-Za-z0-9_$#@!?]+)(i|pv)");

  string stripNs(string s) {
    return regex_replace(s,RRR,"$2");
  }
  
  bool isSmackProc(string s) {
    return regex_match(s,SMACKKW);
  }

}
