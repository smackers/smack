//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/Naming.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Constants.h"
#include <sstream>

namespace smack {

const string Naming::BLOCK_LBL = "$bb";
const string Naming::RET_VAR = "$r";
const string Naming::EXN_VAR = "$exn";
const string Naming::EXN_VAL_VAR = "$exnv";
const string Naming::BOOL_VAR = "$b";
const string Naming::FLOAT_VAR = "$f";
const string Naming::INT_VAR = "$i";
const string Naming::PTR_VAR = "$p";
const string Naming::UNDEF_SYM = "$u";

Regex Naming::BPL_KW(
  "^(bool|int|real|false|true|old|forall|exists|requires|modifies|ensures|invariant|free"
  "|unique|finite|complete|type|const|function|axiom|var|procedure"
  "|implementation|where|returns|assume|assert|havoc|call|return|while"
  "|break|goto|if|else|div|mod|yield|par|async|lambda)$");

Regex Naming::SMACK_NAME(".*__SMACK_.*");

bool Naming::isBplKeyword(string s) {
  return BPL_KW.match(s);
}

bool Naming::isSmackName(string n) {
  return SMACK_NAME.match(n);
}

bool Naming::isSmackGeneratedName(string n) {
  return n.size() > 0 && n[0] == '$';
}

string Naming::escape(string s) {
  string Str(llvm::DOT::EscapeString(s));
  for (unsigned i = 0; i != Str.length(); ++i)
    switch (Str[i]) {
    case '\01':
      Str[i] = '_';
      break;
    case '@':
      Str[i] = '.';
      break;
    }
  return Str;
}

void Naming::reset() {
  blockNum = 0;
  varNum = 0;
}

string Naming::get(const llvm::Value& V) {

  if (names.count(&V))
    return names[&V];

  string name;

  if (V.hasName() && !llvm::isa<llvm::Instruction>(&V)) {
    name = escape(V.getName().str());
    if (isBplKeyword(name))
      name = name + "_";

  } else if (llvm::isa<llvm::GlobalValue>(&V)) {
    // XXX is this a problem?
    assert( false && "Unexpected unnamed global vlaue." );

  } else if (llvm::isa<llvm::BasicBlock>(&V)) {
    name = freshBlockName();

  } else if (llvm::isa<llvm::UndefValue>(&V)) {
    name = freshUndefName();

  } else if (llvm::isa<llvm::Instruction>(&V)) {
    name = freshVarName(V);

  } else if (llvm::isa<llvm::Argument>(&V)) {
    name = freshVarName(V);

  } else {
    name = "";
  }

  names[&V] = name;
  return name;
}

string Naming::freshBlockName() {
  stringstream s;
  s << BLOCK_LBL << blockNum++;
  return s.str();
}

string Naming::freshUndefName() {
  stringstream s;
  s << UNDEF_SYM << undefNum++;
  return s.str();
}

string Naming::freshVarName(const llvm::Value& V) {
  stringstream s;

  if (V.getType()->isFloatingPointTy())
    s << FLOAT_VAR;

  else if (V.getType()->isIntegerTy())
    s << INT_VAR;

  else
    s << PTR_VAR;

  s << varNum++;
  return s.str();
}

}
