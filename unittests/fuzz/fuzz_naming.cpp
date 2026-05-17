// libFuzzer harness for smack::Naming static helpers.
//
// Naming::isSmackName / isSmackGeneratedName / isBplKeyword / escape /
// getIntWrapFunc are pure string predicates. Crashes here would be
// genuine: invalid utf-8, embedded nul, oversize input. The mutator
// is bytes-as-string; the harness asserts nothing besides "didn't
// crash". libFuzzer's coverage feedback chases the prefix-match +
// keyword-table cases.

#include "smack/Naming.h"

#include "llvm/ADT/StringRef.h"

#include <cstddef>
#include <cstdint>
#include <string>

using namespace smack;

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, std::size_t size) {
  // Treat the input as two strings split at the midpoint. Both
  // predicates run on each half.
  std::size_t mid = size / 2;
  std::string a(reinterpret_cast<const char *>(data), mid);
  std::string b(reinterpret_cast<const char *>(data + mid), size - mid);

  (void)Naming::isSmackName(llvm::StringRef(a));
  (void)Naming::isSmackName(llvm::StringRef(b));
  (void)Naming::isSmackGeneratedName(a);
  (void)Naming::isSmackGeneratedName(b);
  (void)Naming::isBplKeyword(a);
  (void)Naming::isBplKeyword(b);

  // escape mutates + copies — exercise it too.
  std::string escA = Naming::escape(a);
  std::string escB = Naming::escape(b);
  (void)escA;
  (void)escB;

  // Static signed/unsigned wrap-function selectors. Constant output but
  // proves the symbol resolves in the fuzz binary.
  if (size & 1)
    (void)Naming::getIntWrapFunc(true);
  else
    (void)Naming::getIntWrapFunc(false);

  return 0;
}
