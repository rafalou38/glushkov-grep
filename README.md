# Grep - Automates de Glushkov

## Utilisation


Pour compiler le code:
```sh
./build.sh
```

Pour le tester:
```sh
./grep "regex" ./tests/francais.txt
```


### run.sh
Compile et execute le programme
`q` Pour quitter less

```sh
./run.sh "regex" ./test/file.txt
```


## Pour afficher un graphe

Avec uniquement un dump en sortie du programme.
(utilise graphviz et imagemagick pour l'affichage)
```sh
./build.sh

./grep | dot -Tpng | display

./grep > out.dot

dot ./out.dot -Tpng -o out.png
```

