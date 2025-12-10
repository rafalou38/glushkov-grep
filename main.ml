type regexp =
  | Vide
  | Epsilon
  | Lettre of char
  | Ou of regexp * regexp
  | Etoile of regexp
  | Concat of regexp * regexp

(* Q, Sigma, q0, T, Delta *)
(* 
    Q - pas besoin
    Sigma - pas besoin
    q0: liste
    T: liste
    Delta: etat, lettre -> etat
  *)
type afnd = {
  initiaux : char list;
  terminaux : char list;
  delta : (char * char, char) Hashtbl.t;
}

(* qs liste d'états; c caractère -> lister d'états *)
let delta_chap (a : afnd) (qs : char list) (c : char) =
    List.fold_left (fun acc q -> 
        let res = Hashtbl.find_all a.delta (q, c) in res@acc
        (* match res with
            | Some e -> e::acc
            | None -> acc *)
     ) [] qs

let rec delta_chap_et (a: afnd) (qs : char list) (m : char list) = 
    match m with
        | []-> qs
        | c::l -> delta_chap_et a (delta_chap a qs c) l

let match_mot (a:afnd) (mot:string) = 
    let fin = delta_chap_et a a.initiaux (List.of_seq (String.to_seq mot))
    (* fin *)
    in
    (* Verifie que l'ensemble final est inclus dans T *)
    fin <> [] && List.exists (fun q -> List.mem q a.terminaux) fin


let parse_regexp (s : string) : regexp =
    let stack = Stack.create () in
    let n = String.length s in
    let point = ref ( Lettre 'a') in
    (* a-z = 98-122 *)
    for i = int_of_char 'b' to int_of_char 'z' do
        point := Ou(!point, Lettre (char_of_int i))
    done;
    (* for i = int_of_char 'A' to int_of_char 'Z' do
        point := Ou(!point, Lettre (char_of_int i))
    done; *)
    (* for i = int_of_char '0' to int_of_char '9' do
        point := Ou(!point, Lettre (char_of_int i))
    done; *)

    (* let alphabet = "abcdefghijklmnopqrstuvwxyz" in
    String.to_seq alphabet |> Seq.iter (fun c -> point := Ou(!point, Lettre c)); *)

    for i = 0 to n - 1 do
      let c = s.[i] in

      match c with
      | '|' -> (
          let ass = Stack.pop_opt stack in
          let bss = Stack.pop_opt stack in
          match (ass, bss) with
          | Some a, Some b -> Stack.push (Ou (b, a)) stack
          | _ -> failwith "erreur dans la regex (|)")
      | '@' -> (
          let ass = Stack.pop_opt stack in
          let bss = Stack.pop_opt stack in
          match (ass, bss) with
          | Some a, Some b -> Stack.push (Concat (b, a)) stack
          | _ -> failwith "erreur dans la regex (@)")
      | '.' -> (Stack.push !point stack)
      | '*' -> (
          let ass = Stack.pop_opt stack in
          match ass with
          | Some a -> Stack.push (Etoile a) stack
          | _ -> failwith "erreur dans la regex (*)")
      | '&' -> Stack.push Epsilon stack
      | x ->
          Stack.push (Lettre x) stack;
          ()
    done;
    match Stack.pop_opt stack with Some regexp -> regexp | None -> Vide

let r1 =
    Ou
      ( Concat (Lettre 'a', Ou (Lettre 'b', Epsilon)),
        Ou (Lettre 'd', Lettre 'e') )

let r2 = parse_regexp "ab&|de|@|"
(* ((b|&)(d|e))|a *)

(* ab*|ca* *)

let r3 = parse_regexp "ab*@ca*@|"
let r4 = parse_regexp (Parser.parse "ab*|ca*")
(*fct de transition de l'automate *)
(*fct qui linéarise l'expression, il faudra garder 
les associations qq part en memoire *)
let linearise (regex : regexp) =
    let liste_lettres = ref [] in
    (* liste de couples indice lettre *)
    (* On commence à 1 pour réserver 0 pour l'état initial *)
    let i = ref 1 in
    let rec aux r =
        match r with
        | Vide -> ()
        | Epsilon -> ()
        | Lettre x ->
            liste_lettres := (char_of_int !i, x) :: !liste_lettres;
            incr i
        | Concat (a, b) ->
            aux a;
            aux b
        | Ou (a, b) ->
            aux a;
            aux b
        | Etoile a -> aux a
    in
    aux regex;
    !liste_lettres

let constr_lineaire (l : (char * char) list) (reg : regexp) =
    let t = Array.of_list l in
    let i = ref 0 in
    let rec aux r =
        match r with
        | Vide -> Vide
        | Epsilon -> Epsilon
        | Lettre a ->
            let x, y = t.(!i) in
            i := !i + 1;
            Lettre x
        | Ou (a, b) -> Ou (aux a, aux b)
        | Concat (a, b) -> Concat (aux a, aux b)
        | Etoile a -> Etoile (aux a)
    in
    aux reg

let rec est_vide exp =
    match exp with
    | Vide -> true
    | Epsilon -> false
    | Lettre _ -> false
    | Etoile _ -> false
    | Ou (a, b) -> est_vide a && est_vide b
    | Concat (a, b) -> est_vide a || est_vide b

let rec contient_mot_vide exp =
    match exp with
    | Vide -> false
    | Epsilon -> true
    | Lettre _ -> false
    | Etoile _ -> true
    | Ou (a, b) -> contient_mot_vide a || contient_mot_vide b
    | Concat (a, b) -> contient_mot_vide a && contient_mot_vide b

let rec union l1 l2 =
    match l1 with
    | [] -> l2
    | hd :: tl -> if List.mem hd l2 then union tl l2 else hd :: union tl l2

let rec simplify expr =
    match expr with
    | Vide -> expr
    | Epsilon -> expr
    | Lettre _ -> expr
    | Etoile a ->
        let res = simplify a in
        if res = Epsilon then Epsilon else Etoile a
    | Ou (a, b) ->
        let asimp = simplify a in
        let bsimp = simplify b in
        if asimp = Epsilon || bsimp = Epsilon then Epsilon else Ou (a, b)
    | Concat (a, b) ->
        let asimp = simplify a in
        let bsimp = simplify b in
        if asimp = Epsilon && bsimp = Epsilon then Epsilon else Ou (a, b)

let calcul_prefixe (exp : regexp) =
    let pref = ref [] in
    let rec aux e =
        match e with
        | Vide -> ()
        | Epsilon -> ()
        | Lettre x -> pref := x :: !pref
        | Etoile a -> aux a
        | Ou (a, b) ->
            aux a;
            aux b
        | Concat (a, b) ->
            if est_vide b then ()
            else if contient_mot_vide a then (
              aux a;
              aux b)
            else aux a
    in
    aux exp;
    !pref

let calcul_suffixe (exp : regexp) =
    let suff = ref [] in
    let rec aux e =
        match e with
        | Vide -> ()
        | Epsilon -> ()
        | Lettre x -> suff := x :: !suff
        | Etoile a -> aux a
        | Ou (a, b) ->
            aux a;
            aux b
        | Concat (a, b) ->
            if est_vide a then ()
            else if contient_mot_vide b then (
              aux a;
              aux b)
            else aux b
        (* Si b=& ou si b = Etoile alors aux a *)
    in
    aux exp;
    !suff

let calcul_facteurs (exp : regexp) =
    let fact = ref [] in
    let rec aux e =
        match e with
        | Vide -> ()
        | Epsilon -> ()
        | Lettre x -> ()
        | Ou (a, b) ->
            aux a;
            aux b
        | Etoile a ->
            aux a;
            let pre = calcul_prefixe a in
            let suff = calcul_suffixe a in
            List.iter
              (fun c1 ->
                List.iter (fun c2 -> fact := (c2, c1) :: !fact) suff)
              pre
        | Concat (a, b) when est_vide a || est_vide b -> ()
        | Concat (a, b) ->
            aux a;
            aux b;
            let pre = calcul_prefixe b in
            let suff = calcul_suffixe a in
            List.iter
              (fun c1 ->
                List.iter (fun c2 -> fact := (c2, c1) :: !fact) suff)
              pre
    in
    aux exp;
    !fact

let const_automate (exp:regexp) = 
    let e_linearise = linearise exp in
    let n = List.length e_linearise in
    (* indices de 1 à n + EI *)
    let e_lin = Array.make (n + 1) ' ' in
    let rec liste_to_tab l = match l with
        |[] -> ()
        |(ind,lettre)::suite -> e_lin.(int_of_char ind) <- lettre;
                                liste_to_tab suite
    in liste_to_tab e_linearise; 
    let e = constr_lineaire e_linearise exp in
    let fact = calcul_facteurs e in
    let pre = calcul_prefixe e in
    let suf = calcul_suffixe e in
    let etat_initial = '\000' in
    let mot_vide_terminal = ref [] in
    (* List.iter (function a,b -> Printf.printf "%d-%d " (int_of_char a) (int_of_char b)) fact; *)
    if contient_mot_vide exp then begin
        mot_vide_terminal := [etat_initial] end;
    let auto = {initiaux = [etat_initial];
                terminaux = (!mot_vide_terminal)@suf;
                delta = Hashtbl.create 1}
    in
    List.iter (fun (q0,q1) -> (
        
        (* Printf.printf "Ajout de la transition %d -> %d\n" (int_of_char q0) (int_of_char q1); *)
        let carac = e_lin.(int_of_char q1) in 
        (* Printf.printf "=> %d - %d -> %d\n" (int_of_char q0) (int_of_char carac) (int_of_char q1); *)
        Hashtbl.add auto.delta (q0,carac) q1
        
    )) fact;
    List.iter (fun q -> let carac = e_lin.(int_of_char q) in
        Hashtbl.add auto.delta (etat_initial,carac) q) pre;
    auto

    

let main () =
    (* Vérifie que l'expression régulière est bien présente en premier
     argument. Sinon, on affiche un message indiquant comment utiliser
     ce programme et on quitte avec un code d'erreur de `1`. *)
    let argc = Array.length Sys.argv in
    if argc < 2 || argc > 3 then (
      Printf.printf "usage : %s regex [file]\n%!" Sys.argv.(0);
      exit 1);
    let regex_str = Sys.argv.(1) in
    (* S'il y a un deuxième argument c'est qu'il faut lire dans ce
     fichier, sinon, on utilise l'entrée standard. *)
    let input_buffer =
        if argc = 3 then Stdlib.open_in Sys.argv.(2) else Stdlib.stdin
    in
    Printf.printf "* Regexp you entered is '%s'\n* Reading from %s\n\n%!"
      regex_str
      (if argc = 3 then Sys.argv.(2) else "stdin");

    let r = parse_regexp (Parser.parse regex_str) in
    let a = const_automate r in
    try
      while true do
        let line = Stdlib.input_line input_buffer in
        if match_mot a line then
         (Printf.printf "[x] %s\n" line)
          else ()
         (* (Printf.printf "[ ] %s\n" line) *)
      done
    with End_of_file -> ();

    if argc = 3 then Stdlib.close_in input_buffer

let () = main ()

let dump_aut (a: afnd) = 
    let s = Hashtbl.to_seq a.delta in 
    Printf.printf("Digraph{\n");
    List.iter (fun q -> Printf.printf "%d [shape=box];" (int_of_char q)) a.initiaux;
    List.iter (fun q -> Printf.printf "%d [shape=doublecircle];" (int_of_char q)) a.terminaux;
    Seq.iter (function (q1,c), q2 -> Printf.printf "%d->%d[label=\"%c\"];\n" (int_of_char q1) (int_of_char q2) c) s;
    Printf.printf("}\n")
(* 
let r = parse_regexp (Parser.parse "a*a")
let a = const_automate r ;; *)

(* match_mot a "to";; *)

(* print_string (Parser.parse ".*a") *)
(* dump_aut a *)