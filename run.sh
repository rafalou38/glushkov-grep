set -xe

ocamlc ./main.ml -o grep

./grep "$@" | less