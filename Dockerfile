FROM ubuntu:20.04
MAINTAINER Shaobo He <polarishehn@gmail.com>

ENV SMACKDIR /home/user/smack

RUN apt-get update && \
      apt-get -y install \
      software-properties-common \
      wget \
      sudo \
      g++

# Borrowed from JFS
# Create `user` user for container with password `user`.  and give it
# password-less sudo access
RUN useradd -m user && \
    echo user:user | chpasswd && \
    cp /etc/sudoers /etc/sudoers.bak && \
    echo 'user  ALL=(root) NOPASSWD: ALL' >> /etc/sudoers

USER user

# Add the current directory to `/home/user/smack`
ADD --chown=user . $SMACKDIR

# Set the work directory
WORKDIR $SMACKDIR

# Build SMACK
RUN bin/build.sh

# Add envinronment
RUN echo "source /home/user/smack.environment" >> ~/.bashrc
