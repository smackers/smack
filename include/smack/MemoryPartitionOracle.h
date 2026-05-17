//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACK_MEMORYPARTITIONORACLE_H
#define SMACK_MEMORYPARTITIONORACLE_H

#include "llvm/ADT/StringRef.h"

#include <memory>
#include <set>
#include <string>
#include <unordered_map>

namespace llvm {
class Instruction;
class Loop;
class Module;
namespace json {
class Object;
} // namespace json
} // namespace llvm

namespace smack {

class MemoryPartitionOracle {
public:
  using RegionSet = std::set<std::string>;
  struct Effect {
    RegionSet refRegions;
    RegionSet modRegions;
    bool complete = false;
  };
  struct IndirectTargets {
    std::set<std::string> targets;
    bool complete = false;
  };

private:
  std::string producer;
  std::string analysis;
  std::string moduleFingerprint;
  std::unordered_map<std::string, RegionSet> accessRegions;
  std::unordered_map<std::string, Effect> callsiteEffects;
  std::unordered_map<std::string, Effect> functionEffects;
  std::unordered_map<std::string, Effect> loopEffects;
  std::unordered_map<std::string, IndirectTargets> indirectCallTargets;

  static std::unique_ptr<MemoryPartitionOracle>
  parseObject(const llvm::json::Object &root, llvm::StringRef path,
              llvm::StringRef actualFingerprint);

public:
  static std::unique_ptr<MemoryPartitionOracle>
  loadFromFile(llvm::StringRef path, llvm::Module &M);

  static std::unique_ptr<MemoryPartitionOracle> createInMemory(
      std::string producer, std::string analysis,
      std::string moduleFingerprint,
      std::unordered_map<std::string, RegionSet> accessRegions,
      std::unordered_map<std::string, Effect> callsiteEffects,
      std::unordered_map<std::string, Effect> functionEffects,
      std::unordered_map<std::string, Effect> loopEffects,
      std::unordered_map<std::string, IndirectTargets> indirectCallTargets);

  static std::string instructionKey(const llvm::Instruction &I);
  static std::string accessKey(const llvm::Instruction &I);
  static bool isSupportedAccess(const llvm::Instruction &I);
  static bool isSupportedCallsite(const llvm::Instruction &I);
  static std::string moduleAccessFingerprint(const llvm::Module &M);

  const RegionSet *lookup(llvm::StringRef key) const;
  const Effect *lookupCallsiteEffect(llvm::StringRef key) const;
  const Effect *lookupFunctionEffect(llvm::StringRef functionName) const;
  const Effect *lookupLoopEffect(llvm::StringRef key) const;
  const IndirectTargets *lookupIndirectCallTargets(llvm::StringRef key) const;
  unsigned accessCount() const { return accessRegions.size(); }
  unsigned callsiteEffectCount() const { return callsiteEffects.size(); }
  unsigned functionEffectCount() const { return functionEffects.size(); }
  unsigned loopEffectCount() const { return loopEffects.size(); }
  unsigned indirectCallTargetCount() const { return indirectCallTargets.size(); }
  llvm::StringRef getProducer() const { return producer; }
  llvm::StringRef getAnalysis() const { return analysis; }
  llvm::StringRef getModuleFingerprint() const { return moduleFingerprint; }
};

} // namespace smack

#endif // SMACK_MEMORYPARTITIONORACLE_H
