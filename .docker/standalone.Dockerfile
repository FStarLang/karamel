# This Dockerfile should be run from the root Karamel directory

FROM ubuntu:22.04

# CI dependencies: opam, jq (to identify F* branch)
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
      jq \
      ca-certificates \
      curl \
      wget \
      git \
      gawk \
      coreutils \
      sudo \
      opam \
      python3 \
      python3-distutils \
      rust-all \
      time


# Create a new user and give them sudo rights
# NOTE: we give them the name "opam" to keep compatibility with
# derived hierarchical CI
RUN useradd -d /home/opam opam
RUN echo 'opam ALL=NOPASSWD: ALL' >> /etc/sudoers
RUN mkdir /home/opam
RUN chown opam:opam /home/opam
USER opam
ENV HOME /home/opam
WORKDIR $HOME
SHELL ["/bin/bash", "--login", "-c"]

# Install OCaml
ARG OCAML_VERSION=4.14.0
RUN opam init --compiler=$OCAML_VERSION --disable-sandboxing 
RUN opam env --set-switch | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile
# unsafe-yes necessary to handle automatic system dependency changes with depext
# See https://github.com/ocaml/opam/issues/4814
ENV OPAMCONFIRMLEVEL=unsafe-yes

ADD --chown=opam:opam ./ $HOME/karamel/
WORKDIR $HOME/karamel

# Dependencies (F* and opam packages)
ENV FSTAR_HOME=$HOME/FStar
RUN eval $(opam env) && .docker/build/install-deps.sh

# CI dependencies: node.js, ctypes-foreign
RUN opam depext ctypes-foreign uucp
RUN opam install ctypes-foreign uucp
RUN curl -fsSL https://deb.nodesource.com/setup_16.x | sudo -E bash -
RUN sudo apt-get install -y --no-install-recommends nodejs

# CI dependencies: sphinx (for the docs)
# sudo pip3 because of https://bugs.launchpad.net/ubuntu/+source/bash/+bug/1588562
# jinja2==3.0.0 because of https://github.com/mkdocs/mkdocs/issues/2799
RUN sudo apt-get install --yes --no-install-recommends python3-pip python3-setuptools python3-distutils
RUN sudo pip3 install --break-system-packages pytz tzdata sphinx==1.7.2 jinja2==3.0.0 alabaster==0.7.13 sphinx_rtd_theme || sudo pip3 install pytz tzdata sphinx==1.7.2 jinja2==3.0.0 alabaster==0.7.13 sphinx_rtd_theme

# CI proper
ARG CI_THREADS=24
ARG CI_BRANCH=master
RUN --mount=type=secret,id=DZOMO_GITHUB_TOKEN eval $(opam env) && DZOMO_GITHUB_TOKEN=$(sudo cat /run/secrets/DZOMO_GITHUB_TOKEN) .docker/build/build-standalone.sh $CI_THREADS $CI_BRANCH
# RUN eval $(opam env) && .docker/build/build-standalone.sh $CI_THREADS $CI_BRANCH

WORKDIR $HOME
ENV KRML_HOME=$HOME/karamel
