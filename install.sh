#!/bin/bash -i

## Place to install TLC, TLAPS, Apalache, ...
mkdir -p tools

WORKDIR="$(pwd)/tools"

## Build custom TLA+ modules
ant -buildfile modules/build.xml dist

## Install TLA+ Tools (download from GitHub)
wget -qN https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar -P tools/
wget -qN https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar -P tools/
echo "alias tlcrepl='java -cp ${WORKDIR}/tla2tools.jar tlc2.REPL'" >> "$HOME/.bashrc"
echo "alias alias tlc='java -XX:+UseParallelGC -cp \"/home/qdelamea/projects/ArmoniK.Spec/tools/*\" tlc2.TLC'"

## Install TLAPS (proof system) and its dependencies
wget -N https://github.com/tlaplus/tlapm/releases/download/1.6.0-pre/tlapm-1.6.0-pre-x86_64-linux-gnu.tar.gz -P /tmp
tar xvfz /tmp/tlapm-1.6.0-pre-x86_64-linux-gnu.tar.gz --directory tools/
sudo apt update && sudo apt install -y opam
opam init -a
echo "export PATH=\$PATH:${WORKDIR}/tlapm/bin" >> "$HOME/.bashrc"

## Install Apalache
wget -qN https://github.com/informalsystems/apalache/releases/latest/download/apalache.tgz -P /tmp
tar xvfz /tmp/apalache.tgz --directory tools/
echo "export PATH=\$PATH:${WORKDIR}/apalache/bin" >> "$HOME/.bashrc"
tools/apalache/bin/apalache-mc config --enable-stats=true

## Install TLAFMT (formatter)
wget -N https://github.com/domodwyer/tlafmt/releases/download/v0.4.1/tlafmt_v0.4.1_x86_64-unknown-linux-musl.tar.gz -P /tmp
tar xvfz /tmp/tlafmt_v0.4.1_x86_64-unknown-linux-musl.tar.gz --directory tools/
mv tools/release/ tools/tlafmt/
mv tools/tlafmt/tlafmt_v0.4.1_x86_64-unknown-linux-musl tools/tlafmt/tlafmt
echo "export PATH=\$PATH:${WORKDIR}/tlafmt" >> "$HOME/.bashrc"
