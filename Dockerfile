FROM ubuntu:24.04 AS dependencies

LABEL org.opencontainers.image.source="https://github.com/smackers/smack"
LABEL org.opencontainers.image.description="SMACK dependencies"
LABEL org.opencontainers.image.authors="Shaobo He <polarishehn@gmail.com>"

ARG DEBIAN_FRONTEND=noninteractive

# build.sh uses sudo even when the image is built as root. The remaining
# packages bootstrap its pinned LLVM, .NET, Boost, Python, and solver installs.
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

# Source changes do not invalidate the dependency stages. Keep this list in
# sync with the files hashed by the CI workflow.
COPY bin/build.sh bin/versions bin/

ENV DEPS_DIR=/opt/smack-deps

RUN BUILD_SMACK=0 \
    TEST_SMACK=0 \
    ./bin/build.sh \
    && rm -rf /var/lib/apt/lists/* /tmp/*

ENV PATH="/opt/smack-deps/z3/bin:/opt/smack-deps/boogie:/opt/smack-deps/corral:${PATH}"
ENV DOTNET_ROLL_FORWARD=Major

# CI also exercises the Rust frontend. This named target is published to GHCR
# and used by the one build job and all regression shards.
FROM dependencies AS ci-deps

RUN INSTALL_DEPENDENCIES=0 \
    INSTALL_RUST=1 \
    INSTALL_Z3=0 \
    INSTALL_BOOGIE=0 \
    INSTALL_CORRAL=0 \
    BUILD_SMACK=0 \
    TEST_SMACK=0 \
    ./bin/build.sh

ENV PATH="/root/.cargo/bin:${PATH}"

# The default target remains the distributable SMACK image built by
# `docker build .` and published from main/develop.
FROM dependencies AS smack

ENV SMACKDIR=/home/user/smack

# Borrowed from JFS: create `user` with password-less sudo access.
RUN useradd -m user \
    && echo user:user | chpasswd \
    && cp /etc/sudoers /etc/sudoers.bak \
    && echo 'user  ALL=(root) NOPASSWD: ALL' >> /etc/sudoers

USER user

COPY --chown=user . ${SMACKDIR}
WORKDIR ${SMACKDIR}

# Dependencies are already present in the shared stage. The solver checks also
# populate smack.environment before the source build and regression tests.
RUN INSTALL_DEPENDENCIES=0 ./bin/build.sh

RUN echo "source /home/user/smack.environment" >> ~/.bashrc
