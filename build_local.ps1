# Look for config.json file
$FILE=".docker/build/config.json"
if ((Test-Path $FILE) -eq $false) {
   Write-Error "File $FILE does not exist."
}

# In case you want to build windows, change agentOS here to windows-nt if OSTYPE is not working
$agentOS = "linux"
if ([environment]::OSVersion.Platform -eq "Win32NT") {
    $agentOS="windows-nt"
}

$DOCKERFILE=(cat ".docker/build/config.json" | ConvertFrom-Json).DockerFile
$DOCKERFILE=$DOCKERFILE.Replace("{agentOS}", $agentOS);

# Copy dockerfile to root
cp $DOCKERFILE ./Dockerfile

# Copy dependencies
$DEPFILES=(cat ".docker/build/config.json" | ConvertFrom-Json).DependencyFiles
cp -r $DEPFILES .

$PROJECTNAME=((cat ".docker/build/config.json" | ConvertFrom-Json).ProjectName).ToLower()
$BUILDTARGET=(cat ".docker/build/config.json" | ConvertFrom-Json).CIBuildTarget
$LOCALBRANCHNAME = (git branch | Select-String -Pattern \*).ToString() | % { $_.Replace("* ", "") }

#Find commit id.
$REQUESTEDBRANCHNAME=(cat ".docker/build/config.json" | ConvertFrom-Json).BranchName
$REQUESTEDCOMMITID=(cat ".docker/build/config.json" | ConvertFrom-Json).BaseContainerImageTagOrCommitId
$COMMITURL=(cat ".docker/build/config.json" | ConvertFrom-Json).GithubCommitUrl

if ((cat ".docker/build/config.json" | ConvertFrom-Json).GithubCommitUrl -ne "latest") {
    $COMMITURL=(cat ".docker/build/config.json" | ConvertFrom-Json).GithubCommitUrl
}

$CONTENT=(Invoke-WebRequest $COMMITURL).Content
$FULLCOMMITID=($CONTENT | % { [regex]::match($_, '/.*commit\/([^"]*).*/') }).Groups[1].Captures[0].Value
$COMMITID= $FULLCOMMITID.SubString(0, 12)

# create fake files ssh key, commitinfofilename.json, etc
echo "fake" > id_rsa
echo "fake" > commitinfofilename.json

# build container
docker build --file Dockerfile --build-arg BUILDLOGFILE="buildlogfile.txt" --build-arg MAXTHREADS="8" --build-arg TARGET="$BUILDTARGET" --build-arg BRANCHNAME="$LOCALBRANCHNAME" --build-arg COMMITID="$COMMITID" --build-arg DOCKERHUBPROJECT="projecteverest/" --tag "$($PROJECTNAME):local" .

# delete fake files
rm id_rsa
rm commitinfofilename.json

# Remove dep files.
$DEPFILES | % { rm  (split-path $_ -leaf)  }

# delete dockerfile
rm Dockerfile