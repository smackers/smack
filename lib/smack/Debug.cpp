#include "smack/Debug.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/circular_raw_ostream.h"
#include "llvm/Support/raw_ostream.h"

#undef isCurrentDebugType
#undef setCurrentDebugType
#undef setCurrentDebugTypes

using namespace llvm;
using namespace smack;

namespace smack {
bool DebugFlag = false;

static ManagedStatic<std::vector<std::string>> CurrentDebugType;

bool isCurrentDebugType(const char *DebugType) {
  if (CurrentDebugType->empty())
    return true;
  for (auto &d : *CurrentDebugType) {
    if (d == DebugType)
      return true;
  }
  return false;
}

void setCurrentDebugTypes(const char **Types, unsigned Count);

void setCurrentDebugType(const char *Type) { setCurrentDebugTypes(&Type, 1); }

void setCurrentDebugTypes(const char **Types, unsigned Count) {
  CurrentDebugType->clear();
  for (size_t T = 0; T < Count; ++T)
    CurrentDebugType->push_back(Types[T]);
}
} // namespace smack

#ifndef NDEBUG

static ::llvm::cl::opt<bool, true> Debug("debug",
                                         cl::desc("Enable debug output"),
                                         cl::Hidden,
                                         cl::location(smack::DebugFlag));

namespace {

struct DebugOnlyOpt {
  void operator=(const std::string &Val) const {
    if (Val.empty())
      return;
    smack::DebugFlag = true;
    SmallVector<StringRef, 8> dbgTypes;
    StringRef(Val).split(dbgTypes, ',', -1, false);
    for (auto dbgType : dbgTypes)
      CurrentDebugType->push_back(dbgType.str());
  }
};
} // namespace

static DebugOnlyOpt DebugOnlyOptLoc;

static ::llvm::cl::opt<DebugOnlyOpt, true, cl::parser<std::string>>
    DebugOnly("debug-only",
              cl::desc("Enable a specific type of debug output "
                       "(comma separated list of types)"),
              cl::Hidden, cl::ZeroOrMore, cl::value_desc("debug string"),
              cl::location(DebugOnlyOptLoc), cl::ValueRequired);

raw_ostream &smack::dbgs() {
  static struct dbgstream {
    circular_raw_ostream strm;

    dbgstream() : strm(errs(), "*** Debug Log Output ***\n", 0) {}
  } thestrm;

  return thestrm.strm;
}

#else
namespace smack {
raw_ostream &dbgs() { return llvm::errs(); }
} // namespace smack

#endif
