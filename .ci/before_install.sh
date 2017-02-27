#!/bin/bash

set -e

echo -e "\e[31m=== Running $0 ===\e[0m"
if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  sudo add-apt-repository --yes ppa:avsm/ppa;
  sudo add-apt-repository --yes ppa:ubuntu-toolchain-r/test;
  sudo add-apt-repository --yes ppa:0k53d-karl-f830m/openssl;
  wget http://llvm.org/releases/3.8.0/clang+llvm-3.8.0-x86_64-linux-gnu-ubuntu-14.04.tar.xz;
  sudo apt-get -qq update;
fi

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  sudo /etc/init.d/postgresql stop;
  for d in postgresql ; do
    sudo rm -rf /var/lib/$d
    sudo mv /var/ramfs/$d /var/lib/
    sudo ln -s /var/lib/$d /var/ramfs/$d
  done
  free -h;
fi
