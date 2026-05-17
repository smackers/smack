#!/bin/bash -eu
# OSS-Fuzz build script. Mirrors what upstream OSS-Fuzz invokes inside
# the project container ($SRC/smack). The OSS-Fuzz framework injects
# $CC, $CXX, $CFLAGS, $CXXFLAGS, $LIB_FUZZING_ENGINE.

cd $SRC/smack

cmake -S . -B build-ossfuzz -GNinja \
  -DSMACK_BUILD_FUZZERS=ON \
  -DCMAKE_C_COMPILER="$CC" \
  -DCMAKE_CXX_COMPILER="$CXX" \
  -DCMAKE_C_FLAGS="$CFLAGS" \
  -DCMAKE_CXX_FLAGS="$CXXFLAGS"

cmake --build build-ossfuzz --target fuzzers -j$(nproc)

# OSS-Fuzz expects the fuzzers + their seed corpora in $OUT. Each
# binary may carry an optional dictionary at <fuzzer>.dict.
for fuzzer in fuzz_bitcode_parse fuzz_boogie_ast_print fuzz_naming; do
  cp "build-ossfuzz/unittests/fuzz/${fuzzer}" "$OUT/"

  # Seed corpus (every harness has one — even if just .gitkeep).
  corpus_dir=""
  case "$fuzzer" in
    fuzz_bitcode_parse)    corpus_dir="unittests/fuzz/corpus/bitcode" ;;
    fuzz_boogie_ast_print) corpus_dir="unittests/fuzz/corpus/boogie_ast" ;;
    fuzz_naming)           corpus_dir="unittests/fuzz/corpus/naming" ;;
  esac
  if [ -d "$corpus_dir" ]; then
    (cd "$corpus_dir" && zip -q "$OUT/${fuzzer}_seed_corpus.zip" . -r) || true
  fi

  # libFuzzer dictionary (optional).
  if [ -f "unittests/fuzz/dict/${fuzzer#fuzz_}.dict" ]; then
    cp "unittests/fuzz/dict/${fuzzer#fuzz_}.dict" "$OUT/${fuzzer}.dict"
  fi
done
