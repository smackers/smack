//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/Naming.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/GraphWriter.h"
#include <sstream>

namespace smack {

const std::string Naming::BOOL_TYPE = "bool";
const std::string Naming::UNINTERPRETED_FLOAT_TYPE = "float";
const std::string Naming::HALF_TYPE = "bvhalf";
const std::string Naming::FLOAT_TYPE = "bvfloat";
const std::string Naming::DOUBLE_TYPE = "bvdouble";
const std::string Naming::LONG_DOUBLE_TYPE = "bvlongdouble";
const std::string Naming::PTR_TYPE = "ref";
const std::string Naming::VECTOR_TYPE = "vec";
const std::string Naming::NULL_VAL = "$0.ref";

const std::string Naming::INIT_FUNC_PREFIX = "__SMACK_init_func";
const std::string Naming::DECLARATIONS_PROC = "__SMACK_decls";

const std::string Naming::CONTRACT_REQUIRES = "__CONTRACT_requires";
const std::string Naming::CONTRACT_ENSURES = "__CONTRACT_ensures";
const std::string Naming::CONTRACT_INVARIANT = "__CONTRACT_invariant";
const std::string Naming::CONTRACT_FORALL = "__CONTRACT_forall";
const std::string Naming::CONTRACT_EXISTS = "__CONTRACT_exists";

const std::string Naming::MOD_PROC = "__SMACK_mod";
const std::string Naming::CODE_PROC = "__SMACK_code";
const std::string Naming::DECL_PROC = "__SMACK_decl";
const std::string Naming::TOP_DECL_PROC = "__SMACK_top_decl";
const std::string Naming::VALUE_PROC = "__SMACK_value";
const std::string Naming::RETURN_VALUE_PROC = "__SMACK_return_value";
const std::string Naming::INITIALIZE_PROC = "$initialize";
const std::string Naming::STATIC_INIT_PROC = "__SMACK_static_init";
const std::string Naming::LOOP_EXIT = "__SMACK_loop_exit";

const std::string Naming::MEMORY = "$M";
const std::string Naming::ALLOC = "$alloc";
const std::string Naming::FREE = "$free";
const std::string Naming::LOAD = "$load";
const std::string Naming::STORE = "$store";
const std::string Naming::MEMCPY = "$memcpy";
const std::string Naming::MEMSET = "$memset";
const std::string Naming::EXTRACT_VALUE = "$extractvalue";
const std::string Naming::MALLOC = "$malloc";

const std::string Naming::EXTERNAL_ADDR = "$isExternal";
const std::string Naming::GLOBALS_BOTTOM = "$GLOBALS_BOTTOM";
const std::string Naming::EXTERNS_BOTTOM = "$EXTERNS_BOTTOM";
const std::string Naming::MALLOC_TOP = "$MALLOC_TOP";

const std::string Naming::BRANCH_CONDITION_ANNOTATION = "branchcond";
const std::string Naming::LOOP_INVARIANT_ANNOTATION = "loopinvariant";

const std::string Naming::MEM_OP = "$mop";
const std::string Naming::REC_MEM_OP = "boogie_si_record_mop";
const std::string Naming::MEM_OP_VAL = "$MOP";

const std::string Naming::RUST_ENTRY = "_ZN3std2rt10lang_start";
const std::string Naming::RUST_LANG_START_INTERNAL =
    "_ZN3std2rt19lang_start_internal";
const std::vector<std::string> Naming::RUST_PANICS = {
    "_ZN3std9panicking15begin_panic_fmt17h", "_ZN4core9panicking5panic17h",
    "_ZN3std9panicking11begin_panic17h", "_ZN4core9panicking9panic_fmt17h",
    "_ZN4core9panicking18panic_bounds_check17h"};

const std::string Naming::RUST_PANIC_ANNOTATION = "rust_panic";

const std::string Naming::RUST_PANIC_MARKER = "__SMACK_RUST_PANIC_MARKER";

const std::string Naming::BLOCK_LBL = "$bb";
const std::string Naming::RET_VAR = "$r";
const std::string Naming::EXN_VAR = "$exn";
const std::string Naming::EXN_VAL_VAR = "$exnv";
const std::string Naming::RMODE_VAR = "$rmode";
const std::string Naming::BOOL_VAR = "$b";
const std::string Naming::FLOAT_VAR = "$f";
const std::string Naming::INT_VAR = "$i";
const std::string Naming::VECTOR_VAR = "$v";
const std::string Naming::PTR_VAR = "$p";
const std::string Naming::GLOBAL_VAR = "$g";
const std::string Naming::UNDEF_SYM = "$u";
const std::string Naming::CONTRACT_EXPR = "$expr";
const std::string Naming::MEMORY_SAFETY_FUNCTION =
    "__SMACK_check_memory_safety";
const std::string Naming::MEMORY_LEAK_FUNCTION = "__SMACK_check_memory_leak";
const std::string Naming::INT_WRAP_SIGNED_FUNCTION = "$tos";
const std::string Naming::INT_WRAP_UNSIGNED_FUNCTION = "$tou";

using namespace llvm;

const std::map<unsigned, std::string> Naming::INSTRUCTION_TABLE{
    {Instruction::Trunc, "$trunc"},
    {Instruction::ZExt, "$zext"},
    {Instruction::SExt, "$sext"},
    {Instruction::FPTrunc, "$fptrunc"},
    {Instruction::FPExt, "$fpext"},
    {Instruction::BitCast, "$bitcast"},
    {Instruction::FPToUI, "$fp2ui"},
    {Instruction::FPToSI, "$fp2si"},
    {Instruction::UIToFP, "$ui2fp"},
    {Instruction::SIToFP, "$si2fp"},
    {Instruction::PtrToInt, "$p2i"},
    {Instruction::IntToPtr, "$i2p"},
    {Instruction::Add, "$add"},
    {Instruction::Sub, "$sub"},
    {Instruction::Mul, "$mul"},
    {Instruction::SDiv, "$sdiv"},
    {Instruction::UDiv, "$udiv"},
    {Instruction::SRem, "$srem"},
    {Instruction::URem, "$urem"},
    {Instruction::And, "$and"},
    {Instruction::Or, "$or"},
    {Instruction::Xor, "$xor"},
    {Instruction::LShr, "$lshr"},
    {Instruction::AShr, "$ashr"},
    {Instruction::Shl, "$shl"},
    {Instruction::FAdd, "$fadd"},
    {Instruction::FSub, "$fsub"},
    {Instruction::FMul, "$fmul"},
    {Instruction::FDiv, "$fdiv"},
    {Instruction::FRem, "$frem"},
    {Instruction::FNeg, "$fneg"},
    {Instruction::ShuffleVector, "$shufflevector"},
    {Instruction::InsertElement, "$insertelement"},
    {Instruction::ExtractElement, "$extractelement"}};

const std::map<unsigned, std::string> Naming::CMPINST_TABLE{
    {CmpInst::ICMP_EQ, "$eq"},        {CmpInst::ICMP_NE, "$ne"},
    {CmpInst::ICMP_SGE, "$sge"},      {CmpInst::ICMP_UGE, "$uge"},
    {CmpInst::ICMP_SLE, "$sle"},      {CmpInst::ICMP_ULE, "$ule"},
    {CmpInst::ICMP_SLT, "$slt"},      {CmpInst::ICMP_ULT, "$ult"},
    {CmpInst::ICMP_SGT, "$sgt"},      {CmpInst::ICMP_UGT, "$ugt"},
    {CmpInst::FCMP_FALSE, "$ffalse"}, {CmpInst::FCMP_OEQ, "$foeq"},
    {CmpInst::FCMP_OGE, "$foge"},     {CmpInst::FCMP_OGT, "$fogt"},
    {CmpInst::FCMP_OLE, "$fole"},     {CmpInst::FCMP_OLT, "$folt"},
    {CmpInst::FCMP_ONE, "$fone"},     {CmpInst::FCMP_ORD, "$ford"},
    {CmpInst::FCMP_TRUE, "$ftrue"},   {CmpInst::FCMP_UEQ, "$fueq"},
    {CmpInst::FCMP_UGE, "$fuge"},     {CmpInst::FCMP_UGT, "$fugt"},
    {CmpInst::FCMP_ULE, "$fule"},     {CmpInst::FCMP_ULT, "$fult"},
    {CmpInst::FCMP_UNE, "$fune"},     {CmpInst::FCMP_UNO, "$funo"}};

const std::map<unsigned, std::string> Naming::ATOMICRMWINST_TABLE{
    {AtomicRMWInst::Add, "$add"},   {AtomicRMWInst::Sub, "$sub"},
    {AtomicRMWInst::And, "$and"},   {AtomicRMWInst::Nand, "$nand"},
    {AtomicRMWInst::Or, "$or"},     {AtomicRMWInst::Xor, "$xor"},
    {AtomicRMWInst::Max, "$smax"},  {AtomicRMWInst::Min, "$smin"},
    {AtomicRMWInst::UMax, "$umax"}, {AtomicRMWInst::UMin, "$umin"}};

Regex Naming::BPL_KW(
    "^(bool|int|real|false|true|old|forall|exists|requires|modifies|ensures|"
    "invariant|free"
    "|unique|finite|complete|type|const|function|axiom|var|procedure"
    "|implementation|where|returns|assume|assert|havoc|call|return|while"
    "|break|goto|if|then|else|div|mod|yield|par|async|lambda)$");

Regex Naming::SMACK_NAME(".*__SMACK_.*");

bool Naming::isBplKeyword(std::string s) { return BPL_KW.match(s); }

bool Naming::isSmackName(llvm::StringRef n) { return SMACK_NAME.match(n); }

bool Naming::isSmackGeneratedName(std::string n) {
  return n.size() > 0 && n[0] == '$';
}

bool Naming::isRustPanic(llvm::StringRef name) {
  for (const auto &panic : Naming::RUST_PANICS) {
    // We are interested in exact functional matches.
    // Rust mangled names include a 17 byte hash at the end.
    if (name.find(panic) == 0 && name.size() == panic.size() + 17) {
      return true;
    }
  }
  return false;
}

std::string Naming::escape(std::string s) {
  std::string Str(s);
  for (unsigned i = 0; i != Str.length(); ++i)
    switch (Str[i]) {
    case '@':
      Str[i] = '.';
      break;
    case '\01':
    case '\\':
    case ':':
    case ' ':
    case '(':
    case ')':
    case '[':
    case ']':
    case '{':
    case '}':
    case '<':
    case '>':
    case '|':
    case '"':
    case '-':
    case ';':
      Str[i] = '_';
      break;
      // Another character to escape would be '$', but SMACK internally
      // generates LLVM IR that uses this character.
    }
  return Str;
}

void Naming::reset() {
  blockNum = 0;
  varNum = 0;
}

std::string Naming::get(const Value &V) {

  if (names.count(&V))
    return names[&V];

  std::string name;

  if (V.hasName() && !isa<Instruction>(&V)) {
    name = escape(V.getName().str());
    if (isBplKeyword(name))
      name = name + "_";

  } else if (isa<GlobalValue>(&V)) {
    name = freshGlobalName();

  } else if (isa<BasicBlock>(&V)) {
    name = freshBlockName();

  } else if (isa<UndefValue>(&V)) {
    name = freshUndefName();

  } else if (isa<Instruction>(&V)) {
    name = freshVarName(V);

  } else if (isa<Argument>(&V)) {
    name = freshVarName(V);

  } else {
    name = "";
  }

  names[&V] = name;
  return name;
}

std::string Naming::freshGlobalName() {
  std::stringstream s;
  s << GLOBAL_VAR << globalNum++;
  return s.str();
}

std::string Naming::freshBlockName() {
  std::stringstream s;
  s << BLOCK_LBL << blockNum++;
  return s.str();
}

std::string Naming::freshUndefName() {
  std::stringstream s;
  s << UNDEF_SYM << undefNum++;
  return s.str();
}

std::string Naming::freshVarName(const Value &V) {
  std::stringstream s;
  const Type *type = V.getType();

  if (type->isFloatingPointTy())
    s << FLOAT_VAR;

  else if (type->isIntegerTy())
    s << INT_VAR;

  else if (type->isVectorTy())
    s << VECTOR_VAR;

  else
    s << PTR_VAR;

  s << varNum++;
  return s.str();
}

std::string Naming::getIntWrapFunc(bool isUnsigned) {
  return isUnsigned ? INT_WRAP_UNSIGNED_FUNCTION : INT_WRAP_SIGNED_FUNCTION;
}
} // namespace smack
