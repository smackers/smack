//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/MemoryPartitionOracle.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

#include <iomanip>
#include <regex>
#include <sstream>
#include <utility>

namespace smack {
namespace {

constexpr uint64_t FnvOffset = 14695981039346656037ULL;
constexpr uint64_t FnvPrime = 1099511628211ULL;

std::string fatalMessage(llvm::StringRef path, llvm::StringRef message) {
  return ("invalid SMACK memory partition oracle " + path + ": " + message)
      .str();
}

void fail(llvm::StringRef path, llvm::StringRef message) {
  llvm::report_fatal_error(llvm::StringRef(fatalMessage(path, message)),
                           false);
}

std::string trimCopy(llvm::StringRef value) {
  return value.trim().str();
}

std::string stripMetadataAttachments(const std::string &text) {
  static const std::regex metadataAttachment(", ![-A-Za-z0-9_.]+ ![0-9]+");
  return std::regex_replace(text, metadataAttachment, "");
}

std::string normalizedInstructionText(const llvm::Instruction &I) {
  std::string text;
  llvm::raw_string_ostream os(text);
  I.print(os);
  os.flush();
  return trimCopy(stripMetadataAttachments(text));
}

std::string hex64(uint64_t value) {
  std::ostringstream os;
  os << std::hex << std::setw(16) << std::setfill('0') << value;
  return os.str();
}

void fnvUpdate(uint64_t &hash, llvm::StringRef value) {
  for (unsigned char c : value.bytes()) {
    hash ^= c;
    hash *= FnvPrime;
  }
  hash ^= '\n';
  hash *= FnvPrime;
}

std::string getStringField(const llvm::json::Object &object,
                           llvm::StringRef field, llvm::StringRef path) {
  auto value = object.getString(field);
  if (!value)
    fail(path, ("missing string field `" + field + "`").str());
  return value->str();
}

MemoryPartitionOracle::RegionSet
parseRegions(const llvm::json::Object &effect, llvm::StringRef field,
             llvm::StringRef path) {
  MemoryPartitionOracle::RegionSet regionSet;
  const llvm::json::Array *regions = effect.getArray(field);
  if (!regions)
    return regionSet;
  for (const auto &region : *regions) {
    auto value = region.getAsString();
    if (!value)
      fail(path, ("effect region id in `" + field + "` must be a string")
                     .str());
    if (!value->empty())
      regionSet.insert(value->str());
  }
  return regionSet;
}

MemoryPartitionOracle::Effect parseEffect(const llvm::json::Value &value,
                                          llvm::StringRef path) {
  const llvm::json::Object *object = value.getAsObject();
  if (!object)
    fail(path, "effect entry must be an object");

  MemoryPartitionOracle::Effect effect;
  effect.refRegions = parseRegions(*object, "ref_regions", path);
  effect.modRegions = parseRegions(*object, "mod_regions", path);
  effect.complete = object->getBoolean("complete").value_or(false);
  return effect;
}

MemoryPartitionOracle::IndirectTargets
parseIndirectTargets(const llvm::json::Value &value, llvm::StringRef path) {
  const llvm::json::Object *object = value.getAsObject();
  if (!object)
    fail(path, "indirect call target entry must be an object");

  MemoryPartitionOracle::IndirectTargets targets;
  targets.complete = object->getBoolean("complete").value_or(false);
  const llvm::json::Array *targetArray = object->getArray("targets");
  if (!targetArray)
    return targets;
  for (const auto &target : *targetArray) {
    auto value = target.getAsString();
    if (!value)
      fail(path, "indirect call target must be a string");
    if (!value->empty())
      targets.targets.insert(value->str());
  }
  return targets;
}

} // namespace

std::unique_ptr<MemoryPartitionOracle>
MemoryPartitionOracle::parseObject(const llvm::json::Object &root,
                                   llvm::StringRef path,
                                   llvm::StringRef actualFingerprint) {
  const int64_t schemaVersion = root.getInteger("schema_version").value_or(-1);
  if (schemaVersion != 1 && schemaVersion != 2 && schemaVersion != 3)
    fail(path, "unsupported schema_version");

  auto oracle = std::make_unique<MemoryPartitionOracle>();
  oracle->producer = getStringField(root, "producer", path);
  oracle->analysis = getStringField(root, "analysis", path);
  oracle->moduleFingerprint = getStringField(root, "module_fingerprint", path);

  if (oracle->moduleFingerprint != actualFingerprint)
    fail(path, "module_fingerprint mismatch");

  const llvm::json::Object *accessRegions = root.getObject("access_regions");
  if (!accessRegions)
    fail(path, "missing object field `access_regions`");

  for (const auto &entry : *accessRegions) {
    const llvm::json::Array *regions = entry.getSecond().getAsArray();
    if (!regions)
      fail(path, "access region entry must be an array");

    MemoryPartitionOracle::RegionSet regionSet;
    for (const auto &region : *regions) {
      auto value = region.getAsString();
      if (!value)
        fail(path, "access region id must be a string");
      if (!value->empty())
        regionSet.insert(value->str());
    }
    oracle->accessRegions[entry.getFirst().str()] = std::move(regionSet);
  }

  if (const llvm::json::Object *callsiteEffects =
          root.getObject("callsite_effects")) {
    for (const auto &entry : *callsiteEffects)
      oracle->callsiteEffects[entry.getFirst().str()] =
          parseEffect(entry.getSecond(), path);
  }

  if (const llvm::json::Object *functionEffects =
          root.getObject("function_effects")) {
    for (const auto &entry : *functionEffects)
      oracle->functionEffects[entry.getFirst().str()] =
          parseEffect(entry.getSecond(), path);
  }

  if (const llvm::json::Object *loopEffects = root.getObject("loop_effects")) {
    for (const auto &entry : *loopEffects)
      oracle->loopEffects[entry.getFirst().str()] =
          parseEffect(entry.getSecond(), path);
  }

  if (const llvm::json::Object *indirectCallTargets =
          root.getObject("indirect_call_targets")) {
    for (const auto &entry : *indirectCallTargets)
      oracle->indirectCallTargets[entry.getFirst().str()] =
          parseIndirectTargets(entry.getSecond(), path);
  }

  return oracle;
}

bool MemoryPartitionOracle::isSupportedAccess(const llvm::Instruction &I) {
  return llvm::isa<llvm::LoadInst>(I) || llvm::isa<llvm::StoreInst>(I);
}

bool MemoryPartitionOracle::isSupportedCallsite(const llvm::Instruction &I) {
  return llvm::isa<llvm::CallBase>(I);
}

std::string MemoryPartitionOracle::instructionKey(const llvm::Instruction &I) {
  const llvm::Function *F = I.getFunction();
  std::string functionName = F && F->hasName() ? F->getName().str() : "";
  return functionName + "\t" + normalizedInstructionText(I);
}

std::string MemoryPartitionOracle::accessKey(const llvm::Instruction &I) {
  return instructionKey(I);
}

std::string MemoryPartitionOracle::moduleAccessFingerprint(
    const llvm::Module &M) {
  uint64_t hash = FnvOffset;
  for (const auto &F : M) {
    if (F.hasName() && F.getName().starts_with("devirtbounce"))
      continue;
    for (const auto &BB : F)
      for (const auto &I : BB)
        if (isSupportedAccess(I))
          fnvUpdate(hash, accessKey(I));
  }
  return hex64(hash);
}

const MemoryPartitionOracle::RegionSet *
MemoryPartitionOracle::lookup(llvm::StringRef key) const {
  auto it = accessRegions.find(key.str());
  if (it == accessRegions.end())
    return nullptr;
  return &it->second;
}

const MemoryPartitionOracle::Effect *
MemoryPartitionOracle::lookupCallsiteEffect(llvm::StringRef key) const {
  auto it = callsiteEffects.find(key.str());
  if (it == callsiteEffects.end())
    return nullptr;
  return &it->second;
}

const MemoryPartitionOracle::Effect *
MemoryPartitionOracle::lookupFunctionEffect(llvm::StringRef functionName) const {
  auto it = functionEffects.find(functionName.str());
  if (it == functionEffects.end())
    return nullptr;
  return &it->second;
}

const MemoryPartitionOracle::Effect *
MemoryPartitionOracle::lookupLoopEffect(llvm::StringRef key) const {
  auto it = loopEffects.find(key.str());
  if (it == loopEffects.end())
    return nullptr;
  return &it->second;
}

const MemoryPartitionOracle::IndirectTargets *
MemoryPartitionOracle::lookupIndirectCallTargets(llvm::StringRef key) const {
  auto it = indirectCallTargets.find(key.str());
  if (it == indirectCallTargets.end())
    return nullptr;
  return &it->second;
}

std::unique_ptr<MemoryPartitionOracle>
MemoryPartitionOracle::loadFromFile(llvm::StringRef path, llvm::Module &M) {
  auto buffer = llvm::MemoryBuffer::getFile(path);
  if (!buffer)
    fail(path, buffer.getError().message());

  auto parsed = llvm::json::parse((*buffer)->getBuffer());
  if (!parsed)
    fail(path, llvm::toString(parsed.takeError()));

  const llvm::json::Object *root = parsed->getAsObject();
  if (!root)
    fail(path, "root must be a JSON object");

  const std::string actualFingerprint = moduleAccessFingerprint(M);
  if (const llvm::json::Object *modules = root->getObject("modules")) {
    const llvm::json::Object *moduleOracle =
        modules->getObject(actualFingerprint);
    if (!moduleOracle)
      fail(path, "no bundled module oracle for module_fingerprint " +
                     actualFingerprint);
    return parseObject(*moduleOracle, path, actualFingerprint);
  }

  return parseObject(*root, path, actualFingerprint);
}

std::unique_ptr<MemoryPartitionOracle> MemoryPartitionOracle::createInMemory(
    std::string producer, std::string analysis, std::string moduleFingerprint,
    std::unordered_map<std::string, RegionSet> accessRegions,
    std::unordered_map<std::string, Effect> callsiteEffects,
    std::unordered_map<std::string, Effect> functionEffects,
    std::unordered_map<std::string, Effect> loopEffects,
    std::unordered_map<std::string, IndirectTargets> indirectCallTargets) {
  auto oracle = std::make_unique<MemoryPartitionOracle>();
  oracle->producer = std::move(producer);
  oracle->analysis = std::move(analysis);
  oracle->moduleFingerprint = std::move(moduleFingerprint);
  oracle->accessRegions = std::move(accessRegions);
  oracle->callsiteEffects = std::move(callsiteEffects);
  oracle->functionEffects = std::move(functionEffects);
  oracle->loopEffects = std::move(loopEffects);
  oracle->indirectCallTargets = std::move(indirectCallTargets);
  return oracle;
}

} // namespace smack
