# This Dockerfile should be run from the root Karamel directory

ARG FSTAR_BRANCH=master
FROM fstar:local-branch-$FSTAR_BRANCH

ADD --chown=opam:opam ./ $HOME/karamel/
WORKDIR $HOME/karamel

# CI dependencies: node.js, ctypes-foreign
RUN opam depext ctypes-foreign
RUN opam install ctypes-foreign
RUN curl -fsSL https://deb.nodesource.com/setup_16.x | sudo -E bash -
RUN sudo apt-get install -y nodejs

# CI proper
ARG CI_THREADS=24
ARG CI_BRANCH=master
RUN eval $(opam env) && .docker/build/build-standalone.sh $CI_THREADS $CI_BRANCH

WORKDIR $HOME
ENV KRML_HOME $HOME/karamel
