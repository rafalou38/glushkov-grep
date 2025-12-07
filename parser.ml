
(* Ordre:
    Syntaxe: 
    - . = ''
    - ? = |eps
    - parentheses
    
    1. *
    2. .
    3. |

*)

type token =
  | CharToken of char
  | StarToken
  | OrToken
  | ConcatToken
  | LToken
  | RToken

let operator_prec (c : token) =
    match c with
    | StarToken -> 5
    | ConcatToken -> 4
    | OrToken -> 3
    | _ -> -1

let is_right_assoc = function StarToken -> true | _ -> false

let token_to_string = function
    | CharToken c -> String.make 1 c
    | StarToken -> "*"
    | ConcatToken -> "."
    | OrToken -> "|"
    | LToken | RToken -> "" (* should not appear in final RPN *)

let parse (s : string) =
    let out_stack : token Stack.t = Stack.create () in
    (* store tokens, not chars *)
    let op_stack : token Stack.t = Stack.create () in
    let n = String.length s in

    (* tokenize avec concat explicite; (a l'envers) *)
    let tokens = ref [] in
    for i = 0 to n - 1 do
      let c = s.[i] in
      match c with
      | '|' -> tokens := OrToken :: !tokens
      | '*' -> tokens := StarToken :: !tokens
      | ')' -> tokens := RToken :: !tokens
      (* Look at the last token to insert concat if needed *)
      | '(' -> (
          match !tokens with
          | CharToken _ :: _ | RToken :: _ | StarToken :: _ ->
              tokens := ConcatToken :: !tokens;
              tokens := LToken :: !tokens
          | _ -> tokens := LToken :: !tokens)
      | _ -> (
          match !tokens with
          | CharToken _ :: _ | RToken :: _ | StarToken :: _ ->
              tokens := ConcatToken :: !tokens;
              tokens := CharToken c :: !tokens
          | _ -> tokens := CharToken c :: !tokens)
    done;

    let pop_op_to_out () =
        if not (Stack.is_empty op_stack) then
          Stack.push (Stack.pop op_stack) out_stack
    in

    let _insert_op (op : token) =
        match op with
        | RToken ->
            (* pop up to LToken *)
            while
              (not (Stack.is_empty op_stack))
              && Stack.top op_stack <> LToken
            do
              pop_op_to_out ()
            done;
            if not (Stack.is_empty op_stack) then (* pop LToken *)
              ignore (Stack.pop op_stack)
        | LToken -> Stack.push LToken op_stack
        | _ ->
            (* regular operator: pop according to precedence/associativity *)
            while
              (not (Stack.is_empty op_stack))
              && Stack.top op_stack <> LToken
              &&
              if is_right_assoc op then
                operator_prec (Stack.top op_stack) > operator_prec op
              else operator_prec (Stack.top op_stack) >= operator_prec op
            do
              pop_op_to_out ()
            done;
            Stack.push op op_stack
    in

    (* process tokens in forward order *)
    List.iter
      (function
        | OrToken -> _insert_op OrToken
        | ConcatToken -> _insert_op ConcatToken
        | StarToken -> _insert_op StarToken
        | RToken -> _insert_op RToken
        | LToken -> _insert_op LToken
        | CharToken c -> Stack.push (CharToken c) out_stack)
      (List.rev !tokens);

    (* pop remaining operators to output *)
    while not (Stack.is_empty op_stack) do
      let t = Stack.pop op_stack in
      match t with
      | LToken | RToken ->
          failwith "Mauvais parenthésage"
      | _ -> Stack.push t out_stack
    done;

    let rpn =
        Stack.fold (fun acc t -> token_to_string t ^ acc) "" out_stack
    in
    rpn
  
