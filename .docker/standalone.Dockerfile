# This Dockerfile should be run from the root FStar directory

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-ocaml-$ocaml_version

ADD --chown=opam:opam ./ karamel/
WORKDIR karamel

# Dependencies (F* and opam packages)
ENV FSTAR_HOME=$HOME/FStar
RUN eval $(opam env) && .docker/build/install-deps.sh

# CI dependencies: node.js, ctypes-foreign
RUN opam depext ctypes-foreign
RUN opam install ctypes-foreign
RUN curl -fsSL https://deb.nodesource.com/setup_16.x | sudo -E bash -
RUN sudo apt-get install -y nodejs

# CI proper
RUN eval $(opam env) && .docker/build/build-standalone.sh
