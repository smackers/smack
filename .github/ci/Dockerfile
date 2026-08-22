FROM ubuntu:24.04

LABEL org.opencontainers.image.source="https://github.com/smackers/smack"
LABEL org.opencontainers.image.description="Build and regression-test dependencies for SMACK"

ARG DEBIAN_FRONTEND=noninteractive

# build.sh uses sudo even when the image is built as root.  The remaining
# packages are the small bootstrap needed before build.sh installs the pinned
# LLVM, .NET, Boost, Python, Rust, Z3, Boogie, and Corral dependencies.
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        ca-certificates \
        g++ \
        lsb-release \
        software-properties-common \
        sudo \
        wget \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /opt/smack

# Keep this copy list in sync with the files hashed by the workflows.  No
# SMACK sources are baked into this image, so source-only changes reuse it.
COPY bin/build.sh bin/versions bin/

ENV DEPS_DIR=/opt/smack-deps

RUN INSTALL_RUST=1 \
    BUILD_SMACK=0 \
    TEST_SMACK=0 \
    ./bin/build.sh \
    && rm -rf /var/lib/apt/lists/* /tmp/*

ENV PATH="/root/.cargo/bin:/opt/smack-deps/z3/bin:/opt/smack-deps/boogie:/opt/smack-deps/corral:${PATH}"
ENV DOTNET_ROLL_FORWARD=Major
