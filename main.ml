let process_line line = Printf.printf "%s\n%!" line

(* Lecture de l'entrée, ligne par ligne *)
let process input =
    try
      while true do
        let line = Stdlib.input_line input in
        process_line line
      done
    with End_of_file -> ()

let main () =
    (* Vérifie que l'expression régulière est bien présente en premier
     argument. Sinon, on affiche un message indiquant comment utiliser
     ce programme et on quitte avec un code d'erreur de `1`. *)
    let argc = Array.length Sys.argv in
    if argc < 2 || argc > 3 then (
      Printf.printf "usage : %s regex [file]\n%!" Sys.argv.(0);
      exit 1);
    (* S'il y a un deuxième argument c'est qu'il faut lire dans ce
     fichier, sinon, on utilise l'entrée standard. *)
    let input =
        if argc = 3 then Stdlib.open_in Sys.argv.(2) else Stdlib.stdin
    in
    Printf.printf "* Regexp you entered is '%s'\n* Reading from %s\n\n%!"
      Sys.argv.(1)
      (if argc = 3 then Sys.argv.(2) else "stdin");
    process input;
    if argc = 3 then Stdlib.close_in input

let () = main ()
