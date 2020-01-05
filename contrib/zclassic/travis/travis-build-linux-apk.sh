#!/bin/bash
set -ev

if [[ -z $TRAVIS_TAG ]]; then
  echo TRAVIS_TAG unset, exiting
  exit 1
fi

BUILD_REPO_URL=https://github.com/ZSLP/electrum-zslp

cd build

git clone --branch $TRAVIS_TAG $BUILD_REPO_URL electrum-zclassic

docker run --rm \
    -v $(pwd):/opt \
    -w /opt/electrum-zclassic \
    -t zebralucky/electrum-dash-winebuild:Linux /opt/build_linux.sh

sudo find . -name '*.po' -delete
sudo find . -name '*.pot' -delete

sudo chown -R 1000 electrum-zclassic

docker run --rm \
    -v $(pwd)/electrum-zclassic:/home/buildozer/build \
    -t zebralucky/electrum-dash-winebuild:Kivy bash -c \
    'rm -rf packages && ./contrib/make_packages && ./contrib/make_apk'
