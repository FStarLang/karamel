# This Dockerfile should be run from the root FStar directory

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-ocaml-$ocaml_version

ADD --chown=opam:opam ./ karamel/
WORKDIR karamel

# CI dependencies: jq (to identify F* branch)
RUN sudo apt-get install -y --no-install-recommends jq

# Dependencies (F* and opam packages)
ENV FSTAR_HOME=$HOME/FStar
RUN eval $(opam env) && .docker/build/install-deps.sh

# CI dependencies: node.js, ctypes-foreign
RUN opam depext ctypes-foreign
RUN opam install ctypes-foreign
RUN curl -fsSL https://deb.nodesource.com/setup_16.x | sudo -E bash -
RUN sudo apt-get install -y --no-install-recommends nodejs

# CI dependencies: sphinx (for the docs)
# sudo pip3 because of https://bugs.launchpad.net/ubuntu/+source/bash/+bug/1588562
# jinja2==3.0.0 because of https://github.com/mkdocs/mkdocs/issues/2799
RUN sudo apt-get install --yes --no-install-recommends python3-pip python3-setuptools python3-distutils
RUN sudo pip3 install sphinx==1.7.2 jinja2==3.0.0 sphinx_rtd_theme

# CI proper
ARG CI_THREADS=24
ARG CI_BRANCH=master
RUN --mount=type=secret,id=DZOMO_GITHUB_TOKEN eval $(opam env) && DZOMO_GITHUB_TOKEN=$(sudo cat /run/secrets/DZOMO_GITHUB_TOKEN) .docker/build/build-standalone.sh $CI_THREADS $CI_BRANCH
