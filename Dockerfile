FROM ubuntu:18.04
MAINTAINER Shaobo He <shaobo@cs.utah.edu>

ENV SMACKDIR /home/user/smack

RUN apt-get update && \
      apt-get -y install \
      software-properties-common \
      wget \
      sudo

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
RUN sudo bin/build.sh

# Add envinronment
RUN echo "source /home/user/smack.environment" >> ~/.bashrc
