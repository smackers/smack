//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "BplPrintUtils.h"

using namespace std;

string smack::translateName(const string name) {
  
  string s = name;
  
  // replace exotic character(s)
  // for (unsigned i=0; i<s.length(); i++)
  //   if (s[i] == '\01')
  //     s[i] = '_';
    
  // avoid using Boogie keywords
  if (isBplKeyword(s))
    return s + "_";
  else
    return s;
  
}

string smack::translateName(const Value* val) {
  // assert(val->hasName() && "Value has to have a name");
  // const string name = EscapeString(val->getName().str());
  // if (isa<GlobalVariable>(val)) {
  //   return "" + name;
  // } else {
  //   return "" + name;
  // }

  string s;
  if (val->hasName())
    s = EscapeString(val->getName().str());
  else {
    // DEBUG(errs() << "Value : " << *val << "\n");
    raw_string_ostream ss(s);
    ss << *val;
    s = s.substr(1);
    s = "$" + EscapeString(s.substr(s.find("%")+1));
  }
  
  return translateName(s);
}
