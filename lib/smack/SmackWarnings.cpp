#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/Support/raw_ostream.h"

#include "smack/SmackOptions.h"
#include "smack/SmackWarnings.h"

#include <algorithm>
#include <set>

namespace smack {
using namespace llvm;

std::string buildDebugInfo(const Instruction *i) {
  std::stringstream ss;
  if (i && i->getMetadata("dbg")) {
    const DebugLoc DL = i->getDebugLoc();
    auto *scope = cast<DIScope>(DL.getScope());

    ss << scope->getFilename().str() << ":" << DL.getLine() << ":"
       << DL.getCol() << ": ";
  }
  return ss.str();
}

bool SmackWarnings::isSufficientWarningLevel(WarningLevel level) {
  return SmackOptions::WarningLevel >= level;
}

SmackWarnings::UnsetFlagsT
SmackWarnings::getUnsetFlags(RequiredFlagsT requiredFlags) {
  UnsetFlagsT ret;
  std::copy_if(requiredFlags.begin(), requiredFlags.end(),
               std::inserter(ret, ret.begin()),
               [](FlagT *flag) { return !*flag; });
  return ret;
}

std::string SmackWarnings::getFlagStr(UnsetFlagsT flags) {
  std::string ret = "";
  for (auto f : flags) {
    if (f->ArgStr.str() == "bit-precise")
      ret += ("--integer-encoding=bit-vector ");
    else
      ret += ("--" + f->ArgStr.str() + " ");
  }
  return ret;
}

void SmackWarnings::warnIfUnsound(std::string name,
                                  RequiredFlagsT requiredFlags,
                                  Block *currBlock, const Instruction *i,
                                  bool ignore) {
  auto unsetFlags = getUnsetFlags(requiredFlags);
  if (unsetFlags.size())
    warnUnsound(name, unsetFlags, currBlock, i, ignore);
}

void SmackWarnings::warnUnsound(std::string unmodeledOpName, Block *currBlock,
                                const Instruction *i, bool ignore) {
  warnUnsound("unmodeled operation " + unmodeledOpName, UnsetFlagsT(),
              currBlock, i, ignore);
}

void SmackWarnings::warnUnsound(std::string name, UnsetFlagsT unsetFlags,
                                Block *currBlock, const Instruction *i,
                                bool ignore) {
  if (!isSufficientWarningLevel(WarningLevel::Unsound))
    return;
  std::string beginning = std::string("llvm2bpl: ") + buildDebugInfo(i);
  std::string end =
      (ignore ? "unsoundly ignoring " : "over-approximating ") + name + ";";
  if (currBlock)
    currBlock->addStmt(Stmt::comment(beginning + "warning: " + end));
  std::string hint = "";
  if (unsetFlags.size())
    hint = (" try adding flag(s): " + getFlagStr(unsetFlags));
  errs() << beginning;
  (SmackOptions::ColoredWarnings ? errs().changeColor(raw_ostream::MAGENTA)
                                 : errs())
      << "warning: ";
  (SmackOptions::ColoredWarnings ? errs().resetColor() : errs())
      << end << hint << "\n";
}

void SmackWarnings::warnIfUnsound(std::string name, FlagT &requiredFlag,
                                  Block *currBlock, const Instruction *i) {
  warnIfUnsound(name, {&requiredFlag}, currBlock, i);
}

void SmackWarnings::warnIfUnsound(std::string name, FlagT &requiredFlag1,
                                  FlagT &requiredFlag2, Block *currBlock,
                                  const Instruction *i) {
  warnIfUnsound(name, {&requiredFlag1, &requiredFlag2}, currBlock, i);
}

void SmackWarnings::warnInfo(std::string info) {
  if (!isSufficientWarningLevel(WarningLevel::Info))
    return;
  errs() << "warning: " << info << "\n";
}
} // namespace smack
