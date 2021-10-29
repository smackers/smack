//
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef NAMING_H
#define NAMING_H

#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Regex.h"
#include <map>
#include <vector>

namespace smack {

using llvm::Regex;
using llvm::Value;

class Naming {
  static Regex BPL_KW;
  static Regex SMACK_NAME;

  std::map<const Value *, std::string> names;
  unsigned blockNum;
  unsigned varNum;
  unsigned undefNum;
  unsigned globalNum;

public:
  static const std::string BOOL_TYPE;
  static const std::string UNINTERPRETED_FLOAT_TYPE;
  static const std::string HALF_TYPE;
  static const std::string FLOAT_TYPE;
  static const std::string DOUBLE_TYPE;
  static const std::string LONG_DOUBLE_TYPE;
  static const std::string PTR_TYPE;
  static const std::string VECTOR_TYPE;
  static const std::string NULL_VAL;

  static const std::string INIT_FUNC_PREFIX;
  static const std::string DECLARATIONS_PROC;

  static const std::string CONTRACT_REQUIRES;
  static const std::string CONTRACT_ENSURES;
  static const std::string CONTRACT_INVARIANT;
  static const std::string CONTRACT_FORALL;
  static const std::string CONTRACT_EXISTS;

  static const std::string MOD_PROC;
  static const std::string CODE_PROC;
  static const std::string DECL_PROC;
  static const std::string TOP_DECL_PROC;
  static const std::string VALUE_PROC;
  static const std::string RETURN_VALUE_PROC;
  static const std::string INITIALIZE_PROC;
  static const std::string STATIC_INIT_PROC;
  static const std::string LOOP_EXIT;

  static const std::string MEMORY;
  static const std::string ALLOC;
  static const std::string FREE;
  static const std::string LOAD;
  static const std::string STORE;
  static const std::string MEMCPY;
  static const std::string MEMSET;
  static const std::string EXTRACT_VALUE;
  static const std::string MALLOC;

  static const std::string EXTERNAL_ADDR;
  static const std::string GLOBALS_BOTTOM;
  static const std::string EXTERNS_BOTTOM;
  static const std::string MALLOC_TOP;

  static const std::string BRANCH_CONDITION_ANNOTATION;
  static const std::string LOOP_INVARIANT_ANNOTATION;

  static const std::string MEM_OP;
  static const std::string REC_MEM_OP;
  static const std::string MEM_OP_VAL;

  static const std::string BLOCK_LBL;
  static const std::string RET_VAR;
  static const std::string EXN_VAR;
  static const std::string EXN_VAL_VAR;
  static const std::string RMODE_VAR;
  static const std::string BOOL_VAR;
  static const std::string FLOAT_VAR;
  static const std::string INT_VAR;
  static const std::string VECTOR_VAR;
  static const std::string PTR_VAR;
  static const std::string GLOBAL_VAR;
  static const std::string UNDEF_SYM;
  static const std::string CONTRACT_EXPR;
  static const std::string MEMORY_SAFETY_FUNCTION;
  static const std::string MEMORY_LEAK_FUNCTION;

  static const std::string RUST_ENTRY;
  static const std::string RUST_LANG_START_INTERNAL;
  static const std::vector<std::string> RUST_PANICS;
  static const std::string RUST_PANIC_ANNOTATION;
  static const std::string RUST_PANIC_MARKER;

  static const std::string INT_WRAP_SIGNED_FUNCTION;
  static const std::string INT_WRAP_UNSIGNED_FUNCTION;
  static const std::map<unsigned, std::string> INSTRUCTION_TABLE;
  static const std::map<unsigned, std::string> CMPINST_TABLE;
  static const std::map<unsigned, std::string> ATOMICRMWINST_TABLE;

  Naming() : blockNum(0), varNum(0), undefNum(0), globalNum(0) {}
  Naming(Naming &n) : blockNum(n.blockNum), varNum(n.varNum) {}

  void reset();
  std::string get(const Value &V);

  std::string freshGlobalName();
  std::string freshBlockName();
  std::string freshUndefName();
  std::string freshVarName(const Value &V);
  static std::string getIntWrapFunc(bool isUnsigned);

  static bool isBplKeyword(std::string s);
  static bool isSmackName(llvm::StringRef s);
  static bool isSmackGeneratedName(std::string s);
  static bool isRustPanic(llvm::StringRef s);
  static std::string escape(std::string s);
};
} // namespace smack

#endif
