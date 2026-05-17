# syntax=docker/dockerfile:1.7
#
# Multi-stage SMACK image.
#   builder: full toolchain + bin/build.sh + sea-dsa + dependency downloads
#   runtime: same Ubuntu base, runtime-only deps, artifacts copied across
#
# Build:   docker build -t smackers/smack .
# Run:     docker run --rm -it smackers/smack
#
ARG UBUNTU_VERSION=24.04

# ---------------------------------------------------------------------------
# Stage 1: builder
# ---------------------------------------------------------------------------
FROM ubuntu:${UBUNTU_VERSION} AS builder
LABEL stage=builder
ENV DEBIAN_FRONTEND=noninteractive \
    SMACKDIR=/home/user/smack

RUN apt-get update && \
    apt-get install -y --no-install-recommends \
      ca-certificates software-properties-common sudo wget g++ && \
    rm -rf /var/lib/apt/lists/*

RUN useradd -m -s /bin/bash user && \
    echo 'user ALL=(root) NOPASSWD: ALL' >> /etc/sudoers

USER user
WORKDIR /home/user

# Bring source in. `.dockerignore` should keep build artifacts out.
COPY --chown=user . ${SMACKDIR}
WORKDIR ${SMACKDIR}

# bin/build.sh installs system deps (apt) under /usr/local and writes
# /home/user/smack-deps and /home/user/smack.environment.
RUN bin/build.sh && \
    sudo rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* /home/user/.cache && \
    find /home/user/smack-deps -name '*.zip' -delete 2>/dev/null || true && \
    find /home/user/smack-deps -name '*.tar.gz' -delete 2>/dev/null || true && \
    find ${SMACKDIR}/build* -type f \( -name '*.o' -o -name '*.a' \) -delete 2>/dev/null || true

# ---------------------------------------------------------------------------
# Stage 2: runtime
# ---------------------------------------------------------------------------
FROM ubuntu:${UBUNTU_VERSION} AS runtime
LABEL maintainer="SMACK contributors" \
      org.opencontainers.image.source="https://github.com/smackers/smack" \
      org.opencontainers.image.description="SMACK bounded software verifier (LLVM 22)"
ENV DEBIAN_FRONTEND=noninteractive \
    SMACKDIR=/home/user/smack \
    LLVM_SHORT_VERSION=22

# Runtime deps only. No -dev headers, no SDK, no compilers SMACK doesn't shell out to.
# clang-22 is required because share/smack/pipeline/frontend.py invokes it at runtime
# to lower C/C++ inputs to LLVM bitcode.
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
      ca-certificates gnupg sudo wget python3 python3-pip \
      python3-yaml python3-psutil python3-toml \
      libboost-system1.83.0 libboost-thread1.83.0 libboost-filesystem1.83.0 \
      libstdc++6 libgomp1 unzip && \
    install -d -m 0755 /etc/apt/keyrings && \
    wget -qO- https://packages.microsoft.com/keys/microsoft.asc \
      | gpg --dearmor -o /etc/apt/keyrings/microsoft.gpg && \
    echo "deb [signed-by=/etc/apt/keyrings/microsoft.gpg] https://packages.microsoft.com/ubuntu/24.04/prod noble main" \
      > /etc/apt/sources.list.d/microsoft.list && \
    wget -qO- https://apt.llvm.org/llvm-snapshot.gpg.key \
      | gpg --dearmor -o /etc/apt/keyrings/llvm.gpg && \
    echo "deb [signed-by=/etc/apt/keyrings/llvm.gpg] http://apt.llvm.org/noble/ llvm-toolchain-noble-${LLVM_SHORT_VERSION} main" \
      > /etc/apt/sources.list.d/llvm.list && \
    apt-get update && \
    apt-get install -y --no-install-recommends \
      dotnet-runtime-8.0 aspnetcore-runtime-8.0 \
      clang-${LLVM_SHORT_VERSION} llvm-${LLVM_SHORT_VERSION}-runtime libllvm${LLVM_SHORT_VERSION} && \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* && \
    useradd -m -s /bin/bash user && \
    echo 'user ALL=(root) NOPASSWD: ALL' >> /etc/sudoers

USER user
WORKDIR /home/user

# Copy the built SMACK tree, its downloaded deps, and the env script.
COPY --from=builder --chown=user /home/user/smack /home/user/smack
COPY --from=builder --chown=user /home/user/smack-deps /home/user/smack-deps
COPY --from=builder --chown=user /home/user/smack.environment /home/user/smack.environment

RUN echo 'source /home/user/smack.environment' >> /home/user/.bashrc

WORKDIR ${SMACKDIR}
CMD ["/bin/bash", "-l"]
