//===- svf_devirt_oracle.cpp ---------------------------------------------===//
//
// Optional SVF-backed devirtualization evidence generator for SMACK's
// devirt comparison harness.
//
// The tool deliberately does not use SVF's generic print-fp answer as the final
// target set.  It asks SVF for the points-to set of the local table/base pointer
// used by an indirect call, then extracts the exact loaded slot from each
// pointed-to constant global object.
//
//===----------------------------------------------------------------------===//

#include "SVF-LLVM/LLVMModule.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "SVFIR/SVFIR.h"
#include "Util/CommandLine.h"
#include "Util/Options.h"
#include "Util/SVFUtil.h"
#include "WPA/Andersen.h"
#include "MemoryModel/PointerAnalysis.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

using namespace SVF;

namespace {

struct ToolOptions {
  std::string OutPath;
  std::string Candidate = "svf-local";
  std::string EntryFunction;
  std::string Analysis = "ander";
  std::string ExtAPIPath;
  bool ModelArrays = false;
  bool ModelConsts = false;
  bool PreFieldSensitive = false;
  bool VtableInSVFIR = false;
};

struct GepPattern {
  const llvm::Value *Base = nullptr;
  std::vector<unsigned> Indices;
};

struct CallsiteResult {
  std::string CallsiteId;
  unsigned CallsiteIndex = 0;
  std::string FunctionName;
  std::string File;
  unsigned Line = 0;
  unsigned Column = 0;
  std::string Instruction;
  bool Complete = false;
  std::string Reason;
  std::vector<std::string> Targets;
  unsigned PointsToCount = 0;
  unsigned ExtractedObjectCount = 0;
  unsigned UnhandledObjectCount = 0;
};

std::string jsonEscape(const std::string &Input) {
  std::string Out;
  for (char C : Input) {
    switch (C) {
    case '\\':
      Out += "\\\\";
      break;
    case '"':
      Out += "\\\"";
      break;
    case '\n':
      Out += "\\n";
      break;
    case '\r':
      Out += "\\r";
      break;
    case '\t':
      Out += "\\t";
      break;
    default:
      if (static_cast<unsigned char>(C) < 0x20) {
        char Buffer[7];
        std::snprintf(Buffer, sizeof(Buffer), "\\u%04x", C);
        Out += Buffer;
      } else {
        Out += C;
      }
      break;
    }
  }
  return Out;
}

std::string llvmValueText(const llvm::Value &V) {
  std::string Text;
  llvm::raw_string_ostream OS(Text);
  V.print(OS);
  return OS.str();
}

const llvm::Value *stripCasts(const llvm::Value *V) {
  while (true) {
    V = V->stripPointerCasts();
    if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
      if (CE->isCast()) {
        V = CE->getOperand(0);
        continue;
      }
    }
    if (const auto *Op = llvm::dyn_cast<llvm::Operator>(V)) {
      if (Op->getOpcode() == llvm::Instruction::BitCast ||
          Op->getOpcode() == llvm::Instruction::AddrSpaceCast) {
        V = Op->getOperand(0);
        continue;
      }
    }
    return V;
  }
}

bool appendGepIndices(const llvm::User *GEP, GepPattern &Pattern) {
  unsigned OperandIndex = 1;
  for (; OperandIndex < GEP->getNumOperands(); ++OperandIndex) {
    const auto *CI =
        llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(OperandIndex));
    if (!CI)
      return false;
    Pattern.Indices.push_back(static_cast<unsigned>(CI->getZExtValue()));
  }
  return true;
}

bool collectGepPattern(const llvm::Value *Ptr, GepPattern &Pattern) {
  Ptr = stripCasts(Ptr);
  if (const auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(Ptr)) {
    GepPattern Prefix;
    if (!collectGepPattern(GEP->getPointerOperand(), Prefix))
      return false;
    Pattern = Prefix;
    return appendGepIndices(GEP, Pattern);
  }
  if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(Ptr)) {
    if (CE->getOpcode() == llvm::Instruction::GetElementPtr) {
      GepPattern Prefix;
      if (!collectGepPattern(CE->getOperand(0), Prefix))
        return false;
      Pattern = Prefix;
      return appendGepIndices(CE, Pattern);
    }
  }
  Pattern.Base = Ptr;
  return true;
}

const llvm::Constant *aggregateElement(const llvm::Constant *C,
                                       unsigned Index) {
  C = llvm::cast<llvm::Constant>(stripCasts(C));
  if (const auto *Struct = llvm::dyn_cast<llvm::ConstantStruct>(C))
    return Struct->getAggregateElement(Index);
  if (const auto *Array = llvm::dyn_cast<llvm::ConstantArray>(C))
    return Array->getAggregateElement(Index);
  if (const auto *Vector = llvm::dyn_cast<llvm::ConstantVector>(C))
    return Vector->getAggregateElement(Index);
  if (const auto *Data = llvm::dyn_cast<llvm::ConstantDataSequential>(C))
    return Data->getElementAsConstant(Index);
  return nullptr;
}

const llvm::Constant *extractSlot(const llvm::Constant *Initializer,
                                  const std::vector<unsigned> &Indices) {
  const llvm::Constant *Current = Initializer;
  unsigned Start = 0;
  if (!Indices.empty() && Indices[0] == 0)
    Start = 1;
  for (unsigned I = Start; I < Indices.size(); ++I) {
    Current = aggregateElement(Current, Indices[I]);
    if (!Current)
      return nullptr;
  }
  return Current;
}

const llvm::Function *constantFunction(const llvm::Constant *C) {
  C = llvm::cast<llvm::Constant>(stripCasts(C));
  if (const auto *F = llvm::dyn_cast<llvm::Function>(C))
    return F;
  if (const auto *Alias = llvm::dyn_cast<llvm::GlobalAlias>(C)) {
    const llvm::Constant *Aliasee = Alias->getAliasee();
    return Aliasee ? constantFunction(Aliasee) : nullptr;
  }
  if (const auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(C)) {
    if (CE->isCast() || CE->getOpcode() == llvm::Instruction::GetElementPtr)
      return constantFunction(CE->getOperand(0));
  }
  return nullptr;
}

std::string sourceFile(const llvm::DILocation *Loc) {
  if (!Loc)
    return "";
  std::string File = Loc->getFilename().str();
  std::string Dir = Loc->getDirectory().str();
  if (!Dir.empty() && !File.empty() && File[0] != '/')
    return Dir + "/" + File;
  return File;
}

std::vector<std::string> filterToolOptions(int Argc, char **Argv,
                                           ToolOptions &Options) {
  static const std::set<std::string> AnalysisFlags = {
      "-ander", "-nander", "-sander", "-sfrander",
      "-steens", "-type",   "-fspta",  "-vfspta"};
  std::vector<std::string> ModuleNames;
  for (int I = 1; I < Argc; ++I) {
    std::string Arg = Argv[I];
    auto ConsumeValue = [&](std::string &Out) {
      if (I + 1 >= Argc) {
        llvm::errs() << "missing value for " << Arg << "\n";
        std::exit(2);
      }
      Out = Argv[++I];
    };

    if (Arg == "--out") {
      ConsumeValue(Options.OutPath);
    } else if (Arg.rfind("--out=", 0) == 0) {
      Options.OutPath = Arg.substr(std::string("--out=").size());
    } else if (Arg == "--candidate") {
      ConsumeValue(Options.Candidate);
    } else if (Arg.rfind("--candidate=", 0) == 0) {
      Options.Candidate = Arg.substr(std::string("--candidate=").size());
    } else if (Arg == "--entry-function") {
      ConsumeValue(Options.EntryFunction);
    } else if (Arg.rfind("--entry-function=", 0) == 0) {
      Options.EntryFunction = Arg.substr(std::string("--entry-function=").size());
    } else if (AnalysisFlags.count(Arg)) {
      Options.Analysis = Arg.substr(1);
    } else if (Arg == "-model-arrays") {
      Options.ModelArrays = true;
    } else if (Arg == "-model-consts") {
      Options.ModelConsts = true;
    } else if (Arg == "-pre-field-sensitive") {
      Options.PreFieldSensitive = true;
    } else if (Arg == "-vt-in-ir") {
      Options.VtableInSVFIR = true;
    } else if (Arg == "-extapi") {
      ConsumeValue(Options.ExtAPIPath);
    } else if (Arg.rfind("-extapi=", 0) == 0) {
      Options.ExtAPIPath = Arg.substr(std::string("-extapi=").size());
    } else if (Arg == "--help" || Arg == "-help" || Arg == "-h") {
      llvm::outs() << "SVF local-slot devirtualization oracle\n\n"
                   << "USAGE:\n  " << Argv[0]
                   << " [SVF flags] [--out PATH] <input-bitcode>\n\n"
                   << "Supported SVF-local flags: -ander, -model-arrays, "
                   << "-model-consts, -pre-field-sensitive, -vt-in-ir, "
                   << "-extapi=PATH\n";
      std::exit(0);
    } else if (!Arg.empty() && Arg[0] == '-') {
      llvm::errs() << "unsupported svf-devirt-oracle option: " << Arg << "\n";
      std::exit(2);
    } else {
      ModuleNames.push_back(Arg);
    }
  }
  return ModuleNames;
}

void applyToolOptions(const ToolOptions &ToolOpts) {
  if (ToolOpts.ModelArrays)
    SVF::Options::ModelArrays.setValue(true);
  if (ToolOpts.ModelConsts)
    SVF::Options::ModelConsts.setValue(true);
  if (ToolOpts.PreFieldSensitive)
    SVF::Options::UsePreCompFieldSensitive.setValue(true);
  if (ToolOpts.VtableInSVFIR)
    const_cast<Option<bool> &>(SVF::Options::VtableInSVFIR).setValue(true);
  if (!ToolOpts.ExtAPIPath.empty())
    const_cast<Option<std::string> &>(SVF::Options::ExtAPIPath)
        .setValue(ToolOpts.ExtAPIPath);
}

PointerAnalysis *runPointerAnalysis(const ToolOptions &Options, SVFIR *PAG) {
  if (Options.Analysis != "ander") {
    llvm::errs() << "svf-devirt-oracle currently supports -ander only, got -"
                 << Options.Analysis << "\n";
    std::exit(2);
  }
  return AndersenWaveDiff::createAndersenWaveDiff(PAG);
}

bool resolveLocalSlot(const llvm::CallBase &CB, PointerAnalysis &PTA, SVFIR *PAG,
                      LLVMModuleSet *LLVMSet, CallsiteResult &Result) {
  const llvm::Value *Called = stripCasts(CB.getCalledOperand());
  const auto *FnLoad = llvm::dyn_cast<llvm::LoadInst>(Called);
  if (!FnLoad) {
    Result.Reason = "called-operand-is-not-load";
    return false;
  }

  GepPattern Pattern;
  if (!collectGepPattern(FnLoad->getPointerOperand(), Pattern) ||
      !Pattern.Base || Pattern.Indices.empty()) {
    Result.Reason = "called-load-pointer-is-not-constant-gep";
    return false;
  }

  const llvm::Value *Base = stripCasts(Pattern.Base);
  if (!LLVMSet->hasValueNode(Base)) {
    Result.Reason = "svf-has-no-value-node-for-gep-base";
    return false;
  }

  NodeID BaseId = LLVMSet->getValueNode(Base);
  const PointsTo &PTS = PTA.getPts(BaseId);
  if (PTS.empty()) {
    Result.Reason = "svf-empty-base-points-to";
    return false;
  }

  std::set<std::string> Targets;
  bool Complete = true;
  Result.PointsToCount = static_cast<unsigned>(PTS.count());
  for (PointsTo::iterator It = PTS.begin(), End = PTS.end(); It != End; ++It) {
    NodeID Obj = *It;
    if (Obj == PAG->getBlackHoleNode() || Obj == PAG->getConstantNode()) {
      ++Result.UnhandledObjectCount;
      Complete = false;
      continue;
    }

    NodeID BaseObj = PAG->getBaseObjVar(Obj);
    const SVFVar *ObjVar = PAG->getGNode(BaseObj);
    if (!LLVMSet->hasLLVMValue(ObjVar)) {
      ++Result.UnhandledObjectCount;
      Complete = false;
      continue;
    }

    const llvm::Value *LLVMValue = LLVMSet->getLLVMValue(ObjVar);
    LLVMValue = stripCasts(LLVMValue);
    const auto *Global = llvm::dyn_cast<llvm::GlobalVariable>(LLVMValue);
    if (!Global || !Global->hasInitializer()) {
      ++Result.UnhandledObjectCount;
      Complete = false;
      continue;
    }

    const llvm::Constant *Slot = extractSlot(Global->getInitializer(),
                                             Pattern.Indices);
    if (!Slot) {
      ++Result.UnhandledObjectCount;
      Complete = false;
      continue;
    }

    if (const llvm::Function *F = constantFunction(Slot)) {
      Targets.insert(F->getName().str());
      ++Result.ExtractedObjectCount;
    } else if (Slot->isNullValue()) {
      ++Result.ExtractedObjectCount;
    } else {
      ++Result.UnhandledObjectCount;
      Complete = false;
    }
  }

  Result.Targets.assign(Targets.begin(), Targets.end());
  Result.Complete = Complete;
  if (Complete)
    Result.Reason = "svf-base-points-to-constant-slot";
  else
    Result.Reason = "svf-local-unhandled-points-to-object";
  return !Targets.empty() || Complete;
}

void writeReport(const ToolOptions &Options, const std::string &ModuleName,
                 const std::vector<CallsiteResult> &Results) {
  std::ostream *Out = &std::cout;
  std::ofstream File;
  if (!Options.OutPath.empty()) {
    File.open(Options.OutPath);
    Out = &File;
  }

  *Out << "{\n";
  *Out << "  \"adapter\": \"svf-local-slot\",\n";
  *Out << "  \"candidate\": \"" << jsonEscape(Options.Candidate) << "\",\n";
  *Out << "  \"module\": \"" << jsonEscape(ModuleName) << "\",\n";
  *Out << "  \"schema_version\": 2,\n";
  *Out << "  \"callsites\": [\n";
  for (size_t I = 0; I < Results.size(); ++I) {
    const CallsiteResult &R = Results[I];
    *Out << "    {\n";
    *Out << "      \"callsite_id\": \"" << jsonEscape(R.CallsiteId) << "\",\n";
    *Out << "      \"callsite_index\": " << R.CallsiteIndex << ",\n";
    *Out << "      \"column\": " << R.Column << ",\n";
    *Out << "      \"complete\": " << (R.Complete ? "true" : "false") << ",\n";
    *Out << "      \"fallback_target_count\": 0,\n";
    *Out << "      \"file\": \"" << jsonEscape(R.File) << "\",\n";
    *Out << "      \"function\": \"" << jsonEscape(R.FunctionName) << "\",\n";
    *Out << "      \"instruction\": \"" << jsonEscape(R.Instruction) << "\",\n";
    *Out << "      \"line\": " << R.Line << ",\n";
    *Out << "      \"points_to_count\": " << R.PointsToCount << ",\n";
    *Out << "      \"reason\": \"" << jsonEscape(R.Reason) << "\",\n";
    *Out << "      \"sea_dsa_complete\": false,\n";
    *Out << "      \"sea_dsa_target_count\": 0,\n";
    *Out << "      \"source\": \"svf-local-slot\",\n";
    *Out << "      \"svf_extracted_object_count\": " << R.ExtractedObjectCount
         << ",\n";
    *Out << "      \"svf_unhandled_object_count\": " << R.UnhandledObjectCount
         << ",\n";
    *Out << "      \"target_count\": " << R.Targets.size() << ",\n";
    *Out << "      \"targets\": [";
    for (size_t T = 0; T < R.Targets.size(); ++T) {
      if (T)
        *Out << ", ";
      *Out << "\"" << jsonEscape(R.Targets[T]) << "\"";
    }
    *Out << "]\n";
    *Out << "    }" << (I + 1 == Results.size() ? "\n" : ",\n");
  }
  *Out << "  ]\n";
  *Out << "}\n";
}

} // namespace

int main(int Argc, char **Argv) {
  ToolOptions Options;
  std::vector<std::string> ModuleNames = filterToolOptions(Argc, Argv, Options);
  if (ModuleNames.empty()) {
    llvm::errs() << "missing input bitcode\n";
    return 2;
  }
  applyToolOptions(Options);

  LLVMModuleSet::buildSVFModule(ModuleNames);
  SVFIRBuilder Builder;
  SVFIR *PAG = Builder.build();
  PointerAnalysis *PTA = runPointerAnalysis(Options, PAG);

  LLVMModuleSet *LLVMSet = LLVMModuleSet::getLLVMModuleSet();
  std::vector<CallsiteResult> Results;
  std::map<std::string, unsigned> FunctionIndirectCounts;

  for (const std::reference_wrapper<llvm::Module> &ModuleRef :
       LLVMSet->getLLVMModules()) {
    llvm::Module &Module = ModuleRef.get();
    for (llvm::Function &F : Module) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!CB)
          continue;
        const llvm::Value *Called = stripCasts(CB->getCalledOperand());
        if (llvm::isa<llvm::Function>(Called))
          continue;

        CallsiteResult Result;
        Result.FunctionName = F.getName().str();
        Result.CallsiteIndex = FunctionIndirectCounts[Result.FunctionName]++;
        Result.CallsiteId = Result.FunctionName + ":indirect:" +
                            std::to_string(Result.CallsiteIndex);
        if (const llvm::DILocation *Loc = I.getDebugLoc().get()) {
          Result.File = sourceFile(Loc);
          Result.Line = Loc->getLine();
          Result.Column = Loc->getColumn();
        }
        Result.Instruction = llvmValueText(I);

        if (!resolveLocalSlot(*CB, *PTA, PAG, LLVMSet, Result))
          Result.Complete = false;
        Results.push_back(std::move(Result));
      }
    }
  }

  writeReport(Options, ModuleNames.front(), Results);
  AndersenWaveDiff::releaseAndersenWaveDiff();
  LLVMModuleSet::releaseLLVMModuleSet();
  return 0;
}
