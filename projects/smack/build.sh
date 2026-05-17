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

# OSS-Fuzz expects the fuzzers + their seed corpora in $OUT.
cp build-ossfuzz/unittests/fuzz/fuzz_bitcode_parse $OUT/

# Bundle seed corpus into the expected <fuzzer>_seed_corpus.zip layout.
if [ -d unittests/fuzz/corpus/bitcode ]; then
  (cd unittests/fuzz/corpus/bitcode && \
    zip -q $OUT/fuzz_bitcode_parse_seed_corpus.zip . -r) || true
fi
