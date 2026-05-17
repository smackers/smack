# OSS-Fuzz worker image for SMACK.
# Upstream OSS-Fuzz builds this from projects/smack/Dockerfile.
FROM gcr.io/oss-fuzz-base/base-builder:latest

# SMACK's apt-side deps. dotnet/Boogie/Corral aren't needed at fuzz time
# (we exercise the translator + LLVM bitcode reader, not the verifier).
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
      ninja-build cmake python3 wget gnupg software-properties-common \
      libboost-all-dev && \
    install -d -m 0755 /etc/apt/keyrings && \
    wget -qO- https://apt.llvm.org/llvm-snapshot.gpg.key \
      | gpg --dearmor -o /etc/apt/keyrings/llvm.gpg && \
    echo "deb [signed-by=/etc/apt/keyrings/llvm.gpg] http://apt.llvm.org/jammy/ llvm-toolchain-jammy-22 main" \
      > /etc/apt/sources.list.d/llvm.list && \
    apt-get update && \
    apt-get install -y --no-install-recommends \
      clang-22 llvm-22 llvm-22-dev libllvm22 && \
    rm -rf /var/lib/apt/lists/*

RUN git clone --depth 1 --recurse-submodules https://github.com/smackers/smack.git $SRC/smack

WORKDIR $SRC/smack
COPY build.sh $SRC/
