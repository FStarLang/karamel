# kremlin build container

# Define on fstar-version.json what FStar base container image
# mitls build should use.
# By default it always look for the latest FStar container available
# In case you would like to reference a specific commit,
# replace latest with the commit id from github using 12 characters.
ARG DOCKERHUBPROJECT
ARG COMMITID
FROM ${DOCKERHUBPROJECT}fstar-windows-nt:${COMMITID}

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG TARGET
ARG BRANCHNAME

# Add ssh key
# We cannot copy directly to the .ssh folder, instead we copy to a temp folder
WORKDIR "everestsshkey"
COPY id_rsa .
WORKDIR ".."

# Now, using bash we copy the file, set the correct security and remove the previous folder
RUN Invoke-BashCmd '"cd .ssh && cp ../everestsshkey/id_rsa . && chmod 600 id_rsa && rm -rf ../everestsshkey"'

# Do some cleanup
RUN Invoke-BashCmd rm -f build.sh build_helper.sh buildlogfile.txt log_no_replay.html log_worst.html orange_status.txt result.txt status.txt commitinfofilename.json

# Copy source files
WORKDIR "kremlin"
COPY / .
WORKDIR ".."

RUN Invoke-BashCmd rm kremlin/Dockerfile kremlin/build.sh kremlin/build_helper.sh kremlin/id_rsa kremlin/commitinfofilename.json

COPY build.sh build.sh
COPY build_helper.sh build_helper.sh

RUN Invoke-BashCmd ./build_helper.sh $Env:TARGET $Env:BUILDLOGFILE $Env:MAXTHREADS $Env:BRANCHNAME '||' true

# Remove ssh key.
RUN Invoke-BashCmd rm .ssh/id_rsa
