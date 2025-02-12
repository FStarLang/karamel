@echo off

REM Crazy rules in batch mean we need this and also using !varsall! in
REM the first block below to get the updated value for the variable.
setlocal EnableDelayedExpansion

IF exist "%ProgramFiles(x86)%\Microsoft Visual Studio\Installer\vswhere.exe" (
  REM Tip: if you start seeing "The input line is too long", while debugging
  REM this script, restart your shell, vcvarsall just keeps stupidly expanding
  REM some env variables
  FOR /F "tokens=*" %%i IN ('"%ProgramFiles(x86)%\Microsoft Visual Studio\Installer\vswhere.exe" -latest -find **/vcvarsall.bat') DO set varsall=%%i
  call "!varsall!" amd64
) ELSE IF NOT "%VS150COMNTOOLS%"=="" (
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
