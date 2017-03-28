@echo off

IF NOT "%VS150COMNTOOLS%"=="" (
  call "%VS150COMNTOOLS%/../../VC/vcvarsall.bat" amd64
) ELSE IF NOT "%VS140COMNTOOLS%"=="" (
  call "%VS140COMNTOOLS%/../../VC/vcvarsall.bat" amd64
) ELSE IF NOT "%VS120COMNTOOLS%"=="" (
  call "%VS120COMNTOOLS%/../../VC/vcvarsall.bat" amd64
) ELSE IF NOT "%VS110COMNTOOLS%"=="" (
  call "%VS110COMNTOOLS%/../../VC/vcvarsall.bat" amd64
) ELSE (
  ECHO "No supported version of MSVC found. Install Visual Studio?"
  EXIT 255
)

cl.exe %*
