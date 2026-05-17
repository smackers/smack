//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/SVFMemoryPartition.h"

#include "smack/MemoryPartitionOracle.h"
#include "smack/SmackOptions.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include <sstream>
#include <unordered_map>
#include <utility>

#ifdef SMACK_ENABLE_INPROCESS_SVF
#include "Graphs/ICFG.h"
#include "Graphs/SVFG.h"
#include "MSSA/MSSAMuChi.h"
#include "MSSA/MemRegion.h"
#include "MSSA/MemSSA.h"
#include "MSSA/SVFGBuilder.h"
#include "MemoryModel/PointerAnalysis.h"
#include "SVF-LLVM/LLVMModule.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "SVFIR/SVFIR.h"
#include "SVFIR/SVFStatements.h"
#include "Util/CommandLine.h"
#include "Util/Options.h"
#include "Util/SVFUtil.h"
#include "WPA/Andersen.h"
#endif

namespace smack {
namespace {

constexpr const char *NullRegion = "__smack_svf_null__";

std::string pointerName(const llvm::Value &V) {
  std::string s;
  llvm::raw_string_ostream os(s);
  V.print(os);
  return os.str();
}

SVFMemoryPartition::Evidence missing(llvm::StringRef reason) {
  SVFMemoryPartition::Evidence evidence;
  evidence.reason = reason.str();
  return evidence;
}

SVFMemoryPartition::Evidence complete(SVFMemoryPartition::RegionSet regions) {
  SVFMemoryPartition::Evidence evidence;
  evidence.complete = !regions.empty();
  evidence.regionIds = std::move(regions);
  if (!evidence.complete)
    evidence.reason = "empty-svf-region-set";
  return evidence;
}

#ifdef SMACK_ENABLE_INPROCESS_SVF

constexpr const char *ConstantRegion = "__smack_svf_constant__";
constexpr const char *EmptyRegion = "__smack_svf_empty__";

using ICFGToInstruction =
    std::unordered_map<const SVF::ICFGNode *, const llvm::Instruction *>;
using ValueToOriginal =
    std::unordered_map<const llvm::Value *, const llvm::Value *>;

bool isKnownEmptyMemoryMapEffect(const llvm::Function *F) {
  if (!F || !F->hasName())
    return false;

  llvm::StringRef name = F->getName();
  return name == "malloc" || name == "free" ||
         name.starts_with("llvm.dbg.") || name.starts_with("llvm.lifetime.") ||
         name == "llvm.assume" || name.starts_with("__VERIFIER_nondet") ||
         name.starts_with("__SMACK_nondet");
}

void mergeEffect(MemoryPartitionOracle::Effect &dst,
                 const MemoryPartitionOracle::Effect &src) {
  dst.refRegions.insert(src.refRegions.begin(), src.refRegions.end());
  dst.modRegions.insert(src.modRegions.begin(), src.modRegions.end());
  dst.complete = dst.complete && src.complete;
}

std::string objectRegionId(SVF::NodeID id) {
  std::ostringstream os;
  os << "svf.obj." << id;
  return os.str();
}

template <typename NodeSet>
SVFMemoryPartition::RegionSet regionsFromNodeSet(const NodeSet &nodes,
                                                 const SVF::SVFIR &pag) {
  SVFMemoryPartition::RegionSet regions;
  for (auto it = nodes.begin(), end = nodes.end(); it != end; ++it) {
    const SVF::NodeID id = *it;
    if (id == pag.getBlackHoleNode()) {
      regions.insert(SVFMemoryPartition::TopRegion);
      continue;
    }
    if (id == pag.getConstantNode()) {
      regions.insert(ConstantRegion);
      continue;
    }
    regions.insert(objectRegionId(pag.getBaseObjVarID(id)));
  }
  return regions;
}

SVFMemoryPartition::RegionSet
regionsFromMemRegion(const SVF::MemRegion *mr, const SVF::SVFIR &pag) {
  if (!mr)
    return {};
  return regionsFromNodeSet(mr->getPointsTo(), pag);
}

template <typename Operators>
SVFMemoryPartition::RegionSet regionsFromMSSAOperators(const Operators &ops,
                                                       const SVF::SVFIR &pag) {
  SVFMemoryPartition::RegionSet regions;
  for (const auto *op : ops) {
    SVFMemoryPartition::RegionSet opRegions =
        regionsFromMemRegion(op->getMR(), pag);
    regions.insert(opRegions.begin(), opRegions.end());
  }
  return regions;
}

const llvm::Instruction *
instructionForICFG(const ICFGToInstruction &icfgToInstruction,
                   const SVF::ICFGNode *node) {
  auto it = icfgToInstruction.find(node);
  return it == icfgToInstruction.end() ? nullptr : it->second;
}

const llvm::Value *originalValueFor(const llvm::Value *V,
                                    const ValueToOriginal *cloneToOriginal) {
  if (!V || !cloneToOriginal)
    return V;
  auto it = cloneToOriginal->find(V);
  return it == cloneToOriginal->end() ? V : it->second;
}

const llvm::Instruction *
originalInstructionFor(const llvm::Instruction *I,
                       const ValueToOriginal *cloneToOriginal) {
  return llvm::dyn_cast_or_null<llvm::Instruction>(
      originalValueFor(I, cloneToOriginal));
}

void applySVFOptions() {
  if (SmackOptions::SVFAnalysis.getValue() != "ander") {
    std::string error = "svf-native currently supports -smack-svf-analysis=ander only";
    llvm::report_fatal_error(llvm::StringRef(error), false);
  }

  const std::string &memPar = SmackOptions::SVFMemoryPartitionMode.getValue();
  if (memPar != "distinct" && memPar != "intra-disjoint" &&
      memPar != "inter-disjoint") {
    std::string error = "unsupported -smack-svf-mem-par: " + memPar;
    llvm::report_fatal_error(llvm::StringRef(error), false);
  }

  static bool memParSet = false;
  if (!memParSet && memPar != "intra-disjoint") {
    if (!const_cast<::OptionMap<SVF::u32_t> &>(SVF::Options::MemPar)
             .parseAndSetValue(memPar)) {
      std::string error = "SVF rejected -smack-svf-mem-par=" + memPar;
      llvm::report_fatal_error(llvm::StringRef(error), false);
    }
    memParSet = true;
  }

  const std::string &extAPI = SmackOptions::SVFExtAPI.getValue();
  if (!extAPI.empty()) {
    const_cast<::Option<std::string> &>(SVF::Options::ExtAPIPath)
        .setValue(extAPI);
    return;
  }

#ifdef SVF_INSTALL_EXTAPI_BC
  const_cast<::Option<std::string> &>(SVF::Options::ExtAPIPath)
      .setValue(SVF_INSTALL_EXTAPI_BC);
#endif
}

void releaseSVFState() {
  SVF::AndersenWaveDiff::releaseAndersenWaveDiff();
  SVF::SVFIR::releaseSVFIR();
  SVF::LLVMModuleSet::releaseLLVMModuleSet();
}

void normalizeStructGEPIndices(llvm::Module &M,
                               ValueToOriginal *cloneToOriginal = nullptr,
                               bool truncateInvalid = false) {
  llvm::SmallVector<llvm::GetElementPtrInst *, 32> worklist;
  for (auto &F : M)
    for (auto &BB : F)
      for (auto &I : BB)
        if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(&I))
          worklist.push_back(GEP);

  llvm::Type *i32 = llvm::Type::getInt32Ty(M.getContext());
  for (llvm::GetElementPtrInst *GEP : worklist) {
    llvm::SmallVector<llvm::Value *, 8> indices;
    bool changed = false;
    bool truncated = false;
    bool trackingTypes = true;
    llvm::Type *flatType = GEP->getSourceElementType();
    llvm::StructType *structOuter = nullptr;
    llvm::VectorType *vectorOuter = nullptr;

    for (auto II = GEP->idx_begin(), IE = GEP->idx_end(); II != IE; ++II) {
      llvm::Value *index = II->get();
      llvm::Type *indexedType = nullptr;

      if (!trackingTypes) {
        indices.push_back(index);
        continue;
      }

      if (structOuter) {
        auto *constant = llvm::dyn_cast<llvm::ConstantInt>(index);
        if (!constant) {
          if (truncateInvalid) {
            changed = true;
            truncated = true;
            break;
          }
          trackingTypes = false;
          indices.push_back(index);
          continue;
        }
        uint64_t field = constant->getZExtValue();
        if (field >= structOuter->getNumElements()) {
          if (truncateInvalid) {
            changed = true;
            truncated = true;
            break;
          }
          trackingTypes = false;
          indices.push_back(index);
          continue;
        }
        if (!index->getType()->isIntegerTy(32)) {
          index = llvm::ConstantInt::get(i32, field);
          changed = true;
        }
        indexedType = structOuter->getElementType(field);
      } else if (vectorOuter) {
        indexedType = vectorOuter->getElementType();
      } else {
        indexedType = flatType;
      }

      indices.push_back(index);
      if (!indexedType) {
        if (truncateInvalid) {
          indices.pop_back();
          changed = true;
          truncated = true;
          break;
        }
        trackingTypes = false;
        continue;
      }

      structOuter = nullptr;
      vectorOuter = nullptr;
      flatType = nullptr;
      if (auto *arrayType = llvm::dyn_cast<llvm::ArrayType>(indexedType))
        flatType = arrayType->getElementType();
      else if (auto *nextVector = llvm::dyn_cast<llvm::VectorType>(indexedType))
        vectorOuter = nextVector;
      else if (auto *nextStruct = llvm::dyn_cast<llvm::StructType>(indexedType))
        structOuter = nextStruct;
    }
    while (!truncated && indices.size() < GEP->getNumIndices()) {
      auto II = GEP->idx_begin();
      std::advance(II, indices.size());
      indices.push_back(II->get());
    }

    if (!changed)
      continue;

    if (indices.empty()) {
      GEP->replaceAllUsesWith(GEP->getPointerOperand());
      GEP->eraseFromParent();
      continue;
    }

    auto *replacement = llvm::GetElementPtrInst::Create(
        GEP->getSourceElementType(), GEP->getPointerOperand(), indices,
        GEP->getNoWrapFlags(), "", GEP->getIterator());
    replacement->takeName(GEP);
    replacement->setDebugLoc(GEP->getDebugLoc());
    replacement->copyMetadata(*GEP);
    if (cloneToOriginal) {
      auto original = cloneToOriginal->find(GEP);
      if (original != cloneToOriginal->end())
        (*cloneToOriginal)[replacement] = original->second;
    }
    GEP->replaceAllUsesWith(replacement);
    GEP->eraseFromParent();
  }
}

void collectICFGMap(llvm::Module &M, SVF::LLVMModuleSet &llvmSet,
                    ICFGToInstruction &icfgToInstruction) {
  for (const auto &F : M)
    for (const auto &BB : F)
      for (const auto &I : BB)
        if (llvmSet.hasICFGNode(&I))
          icfgToInstruction[llvmSet.getICFGNode(&I)] = &I;
}

void collectPointerValues(llvm::Module &M, SVF::LLVMModuleSet &llvmSet,
                          SVF::PointerAnalysis &pta, SVF::SVFIR &pag,
                          std::unordered_map<const llvm::Value *,
                                             SVFMemoryPartition::RegionSet>
                              &pointerRegions,
                          const ValueToOriginal *cloneToOriginal = nullptr) {
  auto addValue = [&](const llvm::Value *V) {
    if (!V || !V->getType()->isPointerTy())
      return;
    const llvm::Value *key = originalValueFor(V, cloneToOriginal);
    if (llvm::isa<llvm::ConstantPointerNull>(V)) {
      pointerRegions[key].insert(NullRegion);
      return;
    }
    if (!llvmSet.hasValueNode(V)) {
      pointerRegions[key].insert(SVFMemoryPartition::TopRegion);
      return;
    }
    SVFMemoryPartition::RegionSet regions =
        regionsFromNodeSet(pta.getPts(llvmSet.getValueNode(V)), pag);
    if (regions.empty())
      regions.insert(EmptyRegion);
    pointerRegions[key] = std::move(regions);
  };

  for (const auto &G : M.globals())
    addValue(&G);
  for (const auto &A : M.aliases())
    addValue(&A);
  for (const auto &F : M) {
    if (F.getType()->isPointerTy())
      addValue(&F);
    for (const auto &A : F.args())
      addValue(&A);
    for (const auto &BB : F) {
      for (const auto &I : BB) {
        addValue(&I);
        for (const llvm::Use &U : I.operands())
          addValue(U.get());
      }
    }
  }
}

void collectAccessRegions(
    SVF::MemSSA &mssa, const ICFGToInstruction &icfgToInstruction,
    const SVF::SVFIR &pag,
    std::unordered_map<const llvm::Value *, SVFMemoryPartition::RegionSet>
        &loadRegions,
    std::unordered_map<const llvm::Value *, SVFMemoryPartition::RegionSet>
        &storeRegions,
    std::unordered_map<std::string, MemoryPartitionOracle::RegionSet>
        &oracleAccessRegions,
    const ValueToOriginal *cloneToOriginal = nullptr) {
  for (const auto &entry : mssa.getLoadToMUSetMap()) {
    const llvm::Instruction *I =
        instructionForICFG(icfgToInstruction, entry.first->getICFGNode());
    const auto *load = llvm::dyn_cast_or_null<llvm::LoadInst>(I);
    if (!load)
      continue;
    const auto *originalLoad = llvm::dyn_cast_or_null<llvm::LoadInst>(
        originalInstructionFor(load, cloneToOriginal));
    if (!originalLoad)
      originalLoad = load;
    SVFMemoryPartition::RegionSet regions =
        regionsFromMSSAOperators(entry.second, pag);
    if (regions.empty())
      continue;
    loadRegions[originalLoad] = regions;
    oracleAccessRegions[MemoryPartitionOracle::accessKey(*originalLoad)] =
        std::move(regions);
  }

  for (const auto &entry : mssa.getStoreToChiSetMap()) {
    const llvm::Instruction *I =
        instructionForICFG(icfgToInstruction, entry.first->getICFGNode());
    const auto *store = llvm::dyn_cast_or_null<llvm::StoreInst>(I);
    if (!store)
      continue;
    const auto *originalStore = llvm::dyn_cast_or_null<llvm::StoreInst>(
        originalInstructionFor(store, cloneToOriginal));
    if (!originalStore)
      originalStore = store;
    SVFMemoryPartition::RegionSet regions =
        regionsFromMSSAOperators(entry.second, pag);
    if (regions.empty())
      continue;
    storeRegions[originalStore] = regions;
    oracleAccessRegions[MemoryPartitionOracle::accessKey(*originalStore)] =
        std::move(regions);
  }
}

void collectCallsiteEffects(
    SVF::MemSSA &mssa, const ICFGToInstruction &icfgToInstruction,
    const SVF::SVFIR &pag,
    std::unordered_map<std::string, MemoryPartitionOracle::Effect>
        &callsiteEffects,
    const ValueToOriginal *cloneToOriginal = nullptr) {
  for (const auto &entry : mssa.getCallSiteToMuSetMap()) {
    const llvm::Instruction *I =
        instructionForICFG(icfgToInstruction, entry.first);
    if (!I)
      continue;
    const llvm::Instruction *originalI =
        originalInstructionFor(I, cloneToOriginal);
    if (!originalI)
      originalI = I;
    auto &effect =
        callsiteEffects[MemoryPartitionOracle::instructionKey(*originalI)];
    SVFMemoryPartition::RegionSet regions =
        regionsFromMSSAOperators(entry.second, pag);
    effect.refRegions.insert(regions.begin(), regions.end());
    effect.complete = true;
  }

  for (const auto &entry : mssa.getCallSiteToChiSetMap()) {
    const llvm::Instruction *I =
        instructionForICFG(icfgToInstruction, entry.first);
    if (!I)
      continue;
    const llvm::Instruction *originalI =
        originalInstructionFor(I, cloneToOriginal);
    if (!originalI)
      originalI = I;
    auto &effect =
        callsiteEffects[MemoryPartitionOracle::instructionKey(*originalI)];
    SVFMemoryPartition::RegionSet regions =
        regionsFromMSSAOperators(entry.second, pag);
    effect.modRegions.insert(regions.begin(), regions.end());
    effect.complete = true;
  }
}

void collectKnownEmptyCallsites(
    llvm::Module &M,
    std::unordered_map<std::string, MemoryPartitionOracle::Effect>
        &callsiteEffects) {
  for (const auto &F : M)
    for (const auto &BB : F)
      for (const auto &I : BB) {
        const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!CB || !isKnownEmptyMemoryMapEffect(CB->getCalledFunction()))
          continue;
        auto &effect =
            callsiteEffects[MemoryPartitionOracle::instructionKey(I)];
        effect.complete = true;
      }
}

void collectFunctionEffects(
    llvm::Module &M,
    const std::unordered_map<std::string, MemoryPartitionOracle::RegionSet>
        &oracleAccessRegions,
    const std::unordered_map<std::string, MemoryPartitionOracle::Effect>
        &callsiteEffects,
    std::unordered_map<std::string, MemoryPartitionOracle::Effect>
        &functionEffects) {
  for (const auto &F : M) {
    if (!F.hasName())
      continue;

    MemoryPartitionOracle::Effect effect;
    effect.complete = true;
    if (F.isDeclaration()) {
      effect.complete = isKnownEmptyMemoryMapEffect(&F);
      functionEffects[F.getName().str()] = std::move(effect);
      continue;
    }

    for (const auto &BB : F) {
      for (const auto &I : BB) {
        if (const auto *load = llvm::dyn_cast<llvm::LoadInst>(&I)) {
          auto it =
              oracleAccessRegions.find(MemoryPartitionOracle::accessKey(*load));
          if (it == oracleAccessRegions.end()) {
            effect.complete = false;
            continue;
          }
          effect.refRegions.insert(it->second.begin(), it->second.end());
          continue;
        }

        if (const auto *store = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          auto it = oracleAccessRegions.find(
              MemoryPartitionOracle::accessKey(*store));
          if (it == oracleAccessRegions.end()) {
            effect.complete = false;
            continue;
          }
          effect.modRegions.insert(it->second.begin(), it->second.end());
          continue;
        }

        const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!CB)
          continue;
        if (isKnownEmptyMemoryMapEffect(CB->getCalledFunction()))
          continue;
        auto callIt =
            callsiteEffects.find(MemoryPartitionOracle::instructionKey(I));
        if (callIt == callsiteEffects.end()) {
          effect.complete = false;
          continue;
        }
        mergeEffect(effect, callIt->second);
      }
    }

    functionEffects[F.getName().str()] = std::move(effect);
  }
}

void collectIndirectTargets(
    const ICFGToInstruction &icfgToInstruction, SVF::SVFIR &pag,
    SVF::PointerAnalysis &pta, SVF::LLVMModuleSet &llvmSet,
    std::unordered_map<std::string, MemoryPartitionOracle::IndirectTargets>
        &indirectCallTargets,
    const ValueToOriginal *cloneToOriginal = nullptr) {
  for (const auto &entry : pag.getIndirectCallsites()) {
    const llvm::Instruction *I =
        instructionForICFG(icfgToInstruction, entry.first);
    if (!I)
      continue;
    const llvm::Instruction *originalI =
        originalInstructionFor(I, cloneToOriginal);
    if (!originalI)
      originalI = I;

    MemoryPartitionOracle::IndirectTargets targets;
    targets.complete = true;
    const SVF::PointsTo &pts = pta.getPts(entry.second);
    if (pts.empty())
      targets.complete = false;
    for (auto it = pts.begin(), end = pts.end(); it != end; ++it) {
      SVF::NodeID obj = *it;
      if (obj == pag.getBlackHoleNode() || obj == pag.getConstantNode()) {
        targets.complete = false;
        continue;
      }
      const SVF::SVFVar *objVar = pag.getGNode(pag.getBaseObjVarID(obj));
      if (!llvmSet.hasLLVMValue(objVar)) {
        targets.complete = false;
        continue;
      }
      const auto *F =
          llvm::dyn_cast<llvm::Function>(llvmSet.getLLVMValue(objVar));
      if (!F || !F->hasName()) {
        targets.complete = false;
        continue;
      }
      targets.targets.insert(F->getName().str());
    }

    indirectCallTargets[MemoryPartitionOracle::instructionKey(*originalI)] =
        std::move(targets);
  }
}

#endif // SMACK_ENABLE_INPROCESS_SVF

} // namespace

bool SVFMemoryPartition::isAvailable() {
#ifdef SMACK_ENABLE_INPROCESS_SVF
  return true;
#else
  return false;
#endif
}

std::unique_ptr<SVFMemoryPartition> SVFMemoryPartition::build(llvm::Module &M) {
#ifndef SMACK_ENABLE_INPROCESS_SVF
  (void)M;
  llvm::report_fatal_error(
      "svf-native requires SMACK built with -DSMACK_ENABLE_INPROCESS_SVF=ON",
      false);
#else
  applySVFOptions();
  releaseSVFState();

  llvm::ValueToValueMapTy originalToClone;
  std::unique_ptr<llvm::Module> svfInput = llvm::CloneModule(M, originalToClone);
  ValueToOriginal cloneToOriginal;
  for (const auto &entry : originalToClone) {
    const llvm::Value *clone = entry.second;
    if (clone)
      cloneToOriginal[clone] = entry.first;
  }
  normalizeStructGEPIndices(*svfInput, &cloneToOriginal,
                            /*truncateInvalid=*/true);

  auto result = std::unique_ptr<SVFMemoryPartition>(new SVFMemoryPartition());
  std::unordered_map<std::string, MemoryPartitionOracle::RegionSet>
      oracleAccessRegions;
  std::unordered_map<std::string, MemoryPartitionOracle::Effect>
      callsiteEffects;
  std::unordered_map<std::string, MemoryPartitionOracle::Effect>
      functionEffects;
  std::unordered_map<std::string, MemoryPartitionOracle::Effect> loopEffects;
  std::unordered_map<std::string, MemoryPartitionOracle::IndirectTargets>
      indirectCallTargets;

  SVF::LLVMModuleSet::buildSVFModule(*svfInput);
  SVF::LLVMModuleSet *llvmSet = SVF::LLVMModuleSet::getLLVMModuleSet();
  SVF::SVFIRBuilder builder;
  SVF::SVFIR *pag = builder.build();
  SVF::AndersenWaveDiff *pta =
      SVF::AndersenWaveDiff::createAndersenWaveDiff(pag);

  ICFGToInstruction icfgToInstruction;
  collectICFGMap(*svfInput, *llvmSet, icfgToInstruction);
  collectPointerValues(*svfInput, *llvmSet, *pta, *pag, result->pointerRegions,
                       &cloneToOriginal);

  {
    SVF::SVFGBuilder svfgBuilder;
    SVF::SVFG *svfg = svfgBuilder.buildFullSVFG(pta);
    SVF::MemSSA *mssa = svfg ? svfg->getMSSA() : nullptr;
    if (!mssa)
      llvm::report_fatal_error("svf-native failed to build SVF MemorySSA",
                               false);

    collectAccessRegions(*mssa, icfgToInstruction, *pag, result->loadRegions,
                         result->storeRegions, oracleAccessRegions,
                         &cloneToOriginal);
    collectCallsiteEffects(*mssa, icfgToInstruction, *pag, callsiteEffects,
                           &cloneToOriginal);
    collectKnownEmptyCallsites(M, callsiteEffects);
    collectFunctionEffects(M, oracleAccessRegions, callsiteEffects,
                           functionEffects);
    collectIndirectTargets(icfgToInstruction, *pag, *pta, *llvmSet,
                           indirectCallTargets, &cloneToOriginal);
  }

  result->oracle = MemoryPartitionOracle::createInMemory(
      "smack-inprocess-svf", "ander/" +
                                 SmackOptions::SVFMemoryPartitionMode.getValue(),
      MemoryPartitionOracle::moduleAccessFingerprint(M),
      std::move(oracleAccessRegions), std::move(callsiteEffects),
      std::move(functionEffects), std::move(loopEffects),
      std::move(indirectCallTargets));

  releaseSVFState();
  return result;
#endif
}

SVFMemoryPartition::Evidence
SVFMemoryPartition::lookupLoad(const llvm::LoadInst &I) const {
  auto it = loadRegions.find(&I);
  if (it != loadRegions.end())
    return complete(it->second);
  return lookupPointer(*I.getPointerOperand());
}

SVFMemoryPartition::Evidence
SVFMemoryPartition::lookupStore(const llvm::StoreInst &I) const {
  auto it = storeRegions.find(&I);
  if (it != storeRegions.end())
    return complete(it->second);
  return lookupPointer(*I.getPointerOperand());
}

SVFMemoryPartition::Evidence
SVFMemoryPartition::lookupPointer(const llvm::Value &V) const {
  if (llvm::isa<llvm::ConstantPointerNull>(&V)) {
    RegionSet regions;
    regions.insert(NullRegion);
    return complete(std::move(regions));
  }

  auto it = pointerRegions.find(&V);
  if (it != pointerRegions.end())
    return complete(it->second);

  const llvm::Value *stripped = V.stripPointerCasts();
  if (stripped != &V) {
    it = pointerRegions.find(stripped);
    if (it != pointerRegions.end())
      return complete(it->second);
  }

  return missing("svf-native has no points-to region for pointer: " +
                 pointerName(V));
}

} // namespace smack
