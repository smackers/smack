// libFuzzer harness for LLVM bitcode parsing.
//
// SMACK's translator entry point (llvm2bpl) starts by reading an LLVM
// bitcode file. Any crash in the bitcode reader on malformed input
// surfaces in SMACK too. This fuzzer feeds raw mutated bytes into
// parseBitcodeFile + walks a few module-level queries that SMACK's
// passes always touch, so libFuzzer's coverage feedback chases inputs
// that exercise more of the parse path.
//
// Build (clang required):
//   cmake -S . -B build-fuzz \
//     -DSMACK_BUILD_FUZZERS=ON \
//     -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++
//   cmake --build build-fuzz --target fuzz_bitcode_parse
// Run:
//   build-fuzz/unittests/fuzz/fuzz_bitcode_parse \
//     unittests/fuzz/corpus/bitcode -max_total_time=120
//
// Corpus seeds live in unittests/fuzz/corpus/bitcode; checked in so CI
// can run a short (≤2 min) fuzz pass on PRs touching lib/smack.

#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/MemoryBuffer.h"

#include <cstddef>
#include <cstdint>
#include <utility>

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *Data, std::size_t Size) {
  // Bitcode magic is 4 bytes; smaller inputs are guaranteed invalid and
  // don't exercise interesting code paths.
  if (Size < 4)
    return 0;

  llvm::LLVMContext Ctx;
  auto Buf = llvm::MemoryBuffer::getMemBuffer(
      llvm::StringRef(reinterpret_cast<const char *>(Data), Size),
      /*BufferName=*/"fuzz_input",
      /*RequiresNullTerminator=*/false);

  auto Expected = llvm::parseBitcodeFile(Buf->getMemBufferRef(), Ctx);
  if (auto E = Expected.takeError()) {
    // Most random inputs reject here. Drop the error and let libFuzzer
    // mutate again. A crash inside takeError itself is a real bug — it
    // would manifest as ASan/UBSan abort, not the consumeError() below.
    llvm::consumeError(std::move(E));
    return 0;
  }

  llvm::Module &M = **Expected;

  // Touch metadata + function iteration. SMACK's passes always run these
  // on the input module, so any latent reader bug exposed by them is
  // material.
  (void)M.getNamedMetadata("llvm.module.flags");
  (void)M.getModuleIdentifier();
  (void)M.getSourceFileName();
  (void)M.getTargetTriple();

  for (llvm::Function &F : M) {
    (void)F.getName();
    (void)F.empty();
    for (llvm::BasicBlock &BB : F) {
      (void)BB.empty();
      (void)BB.size();
    }
  }

  return 0;
}
