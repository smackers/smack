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
const string Naming::PTR_VAR = "$p";
const string Naming::UNDEF_SYM = "$u";

Regex Naming::BPL_KW(
  "^(bool|int|false|true|old|forall|exists|requires|modifies|ensures|invariant|free"
  "|unique|finite|complete|type|const|function|axiom|var|procedure"
  "|implementation|where|returns|assume|assert|havoc|call|return|while"
  "|break|goto|if|else|div|mod|yield|par|async)$");

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

void Naming::enter() {
  NameMap N;
  nameStack.push(N);
}

void Naming::leave() {
  assert(nameStack.size() > 0 && "Name stack should not be empty.");
  nameStack.pop();
  if (nameStack.size() == 0) {
    varNum = 0;
    blockNum = 0;
  }
}

string Naming::get(const llvm::Value& V) {

  if (nameStack.size() > 0 && nameStack.top().count(&V))
    return nameStack.top()[&V];

  string name;

  if (V.hasName() && !llvm::isa<llvm::Instruction>(&V)) {
    name = escape(V.getName().str());
    if (isBplKeyword(name))
      name = name + "_";

  } else if (llvm::isa<llvm::BasicBlock>(&V)) {
    assert(nameStack.size() > 0 && "Name stack should not be empty.");
    name = freshBlockName();

  } else if (llvm::isa<llvm::UndefValue>(&V)) {
    return freshVarName(V);

  } else if (llvm::isa<llvm::Instruction>(&V)) {
    assert(nameStack.size() > 0 && "Name stack should not be empty.");
    name = freshVarName(V);

  } else {
    name = "";
  }
  
  if (nameStack.size() > 0)
    nameStack.top()[&V] = name;
  return name;
}

string Naming::freshBlockName() {
  stringstream s;
  s << BLOCK_LBL << blockNum++;
  return s.str();
}

string Naming::freshVarName(const llvm::Value& V) {
  stringstream s;

  if (llvm::isa<llvm::UndefValue>(&V))
    s << UNDEF_SYM;

  else if (V.getType()->isIntegerTy(1))
    s << BOOL_VAR;

  else if (V.getType()->isFloatingPointTy())
    s << FLOAT_VAR;

  else
    s << PTR_VAR;

  s << varNum++;
  return s.str();
}

}
