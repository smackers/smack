//
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef SMACKWARNINGS_H
#define SMACKWARNINGS_H

#include "smack/BoogieAst.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/CommandLine.h"

#include <initializer_list>
#include <list>

namespace smack {

class SmackWarnings {
  typedef const llvm::cl::opt<bool> FlagT;
  typedef std::initializer_list<const FlagT *> RequiredFlagsT;
  typedef std::list<const FlagT *> UnsetFlagsT;

public:
  enum class WarningLevel : unsigned {
    Silent = 0,
    Unsound = 10, // Unhandled intrinsics, asm, etc
    Info = 20     // Memory length, etc.
  };

  enum class FlagRelation : unsigned { And = 0, Or = 1 };

  static UnsetFlagsT getUnsetFlags(RequiredFlagsT flags);
  static bool isSatisfied(RequiredFlagsT flags, FlagRelation rel);

  // generate warnings about unsoundness
  static void warnUnsound(std::string unmodeledOpName, Block *currBlock,
                          const llvm::Instruction *i, bool ignore = false,
                          FlagRelation rel = FlagRelation::And);
  static void warnUnsound(std::string name, UnsetFlagsT unsetFlags,
                          Block *currBlock, const llvm::Instruction *i,
                          bool ignore = false,
                          FlagRelation rel = FlagRelation::And);
  static void warnIfUnsound(std::string name, RequiredFlagsT requiredFlags,
                            Block *currBlock, const llvm::Instruction *i,
                            bool ignore = false,
                            FlagRelation rel = FlagRelation::And);
  static void warnIfUnsound(std::string name, FlagT &requiredFlag,
                            Block *currBlock, const llvm::Instruction *i,
                            FlagRelation rel = FlagRelation::And);
  static void warnIfUnsound(std::string name, FlagT &requiredFlag1,
                            FlagT &requiredFlag2, Block *currBlock,
                            const llvm::Instruction *i,
                            FlagRelation rel = FlagRelation::And);

  // generate warnings about memcpy/memset length/DSA
  static void warnInfo(std::string info);

private:
  static bool isSufficientWarningLevel(WarningLevel level);
  static std::string getFlagStr(UnsetFlagsT flags);
};
} // namespace smack

#endif // SMACKWARNINGS_H
