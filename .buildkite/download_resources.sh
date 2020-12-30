#!/bin/bash

set -e

DEB_NAME="kernel-image-4.9.0-13-amd64-di_4.9.228-1_amd64.udeb"
DEB_URL="http://ftp.us.debian.org/debian/pool/main/l/linux/${DEB_NAME}"

TMP_PATH="/tmp/linux-loader/"
DEB_PATH="${TMP_PATH}/${DEB_NAME}"
EXTRACT_PATH="${TMP_PATH}/src/bzimage-archive"
BZIMAGE_PATH="${EXTRACT_PATH}/boot/vmlinuz"
SCRIPTPATH="$( cd "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"

mkdir -p ${EXTRACT_PATH}

curl $DEB_URL -o ${DEB_PATH}
dpkg-deb -x ${DEB_PATH} ${EXTRACT_PATH}

mv ${BZIMAGE_PATH} "${SCRIPTPATH}/../src/loader/x86_64/bzimage/bzimage"
rm -r ${EXTRACT_PATH}
rm -f ${DEB_PATH}
