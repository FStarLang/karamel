# miTLS build container

# Define on fstar-version.json what FStar base container image
# mitls build should use.
# By default it always look for the latest FStar container available
# In case you would like to reference a specific commit,
# replace latest with the commit id from github using 12 characters.
ARG DOCKERHUBPROJECT
ARG COMMITID
FROM ${DOCKERHUBPROJECT}fstar-linux:${COMMITID}

RUN pip3 install --upgrade pip && pip install --user sphinx
RUN yes | sudo pip3 uninstall Pygments && \
    git clone https://github.com/denismerigoux/pygments && \
    cd pygments && \
    git checkout 763/protz/fstar && \
    sudo python3 setup.py install

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG BUILDTARGET
ARG BRANCHNAME

# ADD SSH KEY
RUN mkdir -p ${MYHOME}/.ssh
RUN chown everest ${MYHOME}/.ssh
RUN chmod 700 ${MYHOME}/.ssh
COPY --chown=everest id_rsa ${MYHOME}/.ssh/id_rsa
RUN chmod 600 ${MYHOME}/.ssh/id_rsa

# Remove leftover files resulting from F* build
RUN rm -f build.sh build_helper.sh buildlogfile.txt log_no_replay.html log_worst.html orange_status.txt result.txt status.txt commitinfofilename.json

# Copy source files
RUN mkdir ${MYHOME}/kremlin
COPY --chown=everest / ${MYHOME}/kremlin

# The Azure Devops build copies these files from .docker/linux/, etc. into the
# root of the kremlin git repository.
RUN rm kremlin/Dockerfile kremlin/build.sh kremlin/build_helper.sh kremlin/id_rsa kremlin/commitinfofilename.json

COPY --chown=everest build.sh ${MYHOME}/build.sh
RUN chmod +x build.sh
COPY --chown=everest build_helper.sh ${MYHOME}/build_helper.sh
RUN chmod +x build_helper.sh

RUN ./build_helper.sh ${BUILDTARGET} ${BUILDLOGFILE} ${MAXTHREADS} ${BRANCHNAME} || true

# Remove ssh identities.
RUN rm ${MYHOME}/.ssh/id_rsa
