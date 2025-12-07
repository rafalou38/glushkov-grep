set -xe

ocamlc ./parser.ml
ocamlc ./parser.cmo ./main.ml -o grep

./grep "$@" | less