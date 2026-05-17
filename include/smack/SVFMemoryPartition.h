//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACK_SVF_MEMORY_PARTITION_H
#define SMACK_SVF_MEMORY_PARTITION_H

#include "smack/MemoryPartitionOracle.h"

#include <memory>
#include <string>
#include <unordered_map>

namespace llvm {
class LoadInst;
class Module;
class StoreInst;
class Value;
} // namespace llvm

namespace smack {

class SVFMemoryPartition {
public:
  using RegionSet = MemoryPartitionOracle::RegionSet;

  struct Evidence {
    RegionSet regionIds;
    bool complete = false;
    std::string reason;
  };

  static constexpr const char *TopRegion = "__smack_svf_top__";

  static bool isAvailable();
  static std::unique_ptr<SVFMemoryPartition> build(llvm::Module &M);

  const MemoryPartitionOracle *getOracle() const { return oracle.get(); }

  Evidence lookupLoad(const llvm::LoadInst &I) const;
  Evidence lookupStore(const llvm::StoreInst &I) const;
  Evidence lookupPointer(const llvm::Value &V) const;

private:
  using ValueRegionMap = std::unordered_map<const llvm::Value *, RegionSet>;

  ValueRegionMap pointerRegions;
  ValueRegionMap loadRegions;
  ValueRegionMap storeRegions;
  std::unique_ptr<MemoryPartitionOracle> oracle;
};

} // namespace smack

#endif // SMACK_SVF_MEMORY_PARTITION_H
