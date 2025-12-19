set -xe

# ocamlc ./parser.ml
# ocamlc ./parser.cmo ./main.ml -o grep


ocamlopt -O3 ./parser.ml
ocamlopt -O3 ./parser.cmx ./main.ml -o grep