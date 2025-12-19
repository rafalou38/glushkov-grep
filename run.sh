set -xe

./build.sh

./grep "$@" | less