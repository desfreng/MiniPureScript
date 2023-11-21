type ind = Mark | Bloc of int

let waiting_tokens = Queue.create ()
let s = Stack.create ()

(** Pop element out of the stack until we found a (Bloc x) with x <= n
    Operate only if not in weak_mode *)
let close c weak_mode =
  if weak_mode then ()
  else
    let rec loop () =
      match Stack.top_opt s with
      | None -> () (* Nothing to close *)
      | Some Mark -> () (* Found a Mark, Nothing to close either *)
      | Some (Bloc n) when n > c ->
          (* Closing a more indented bloc *)
          Stack.drop s;
          Queue.add Parser.RACC waiting_tokens;
          loop ()
      | Some (Bloc n) when n = c ->
          (* Found a bloc we fit in, adding a ; to pass to the next expr *)
          Queue.add Parser.SEMICOLON waiting_tokens
      | Some (Bloc _) -> () (* Bloc too under-indented to be closed *)
    in
    loop ()

(** Pop element until a Mark is found *)
let rec unstack () =
  match Stack.top_opt s with
  | None -> () (* Nothing to close *)
  | Some Mark -> Stack.drop s (* We drop the mark we found *)
  | Some (Bloc _) ->
      (* Close the bloc and search a Mark deeper in the stack *)
      Queue.add Parser.RACC waiting_tokens;
      Stack.drop s;
      unstack ()

let process_tokens lexbuf =
  let rec process_tokens (t : Lexer.pretoken) weak_mode =
    match t.t with
    | IF | LPAR | CASE ->
        close t.col weak_mode;
        Stack.push Mark s;
        Queue.add t.t waiting_tokens
    | RPAR | THEN | ELSE | IN ->
        unstack ();
        if t.t = THEN then Stack.push Mark s;
        Queue.add t.t waiting_tokens
    | WHERE | DO | LET | OF ->
        close t.col weak_mode;
        if t.t = LET then Stack.push Mark s else if t.t = OF then unstack ();
        Queue.add t.t waiting_tokens;
        Queue.add Parser.LACC waiting_tokens;
        let tok = Lexer.gen_pretokens lexbuf in
        close tok.col weak_mode;
        Stack.push (Bloc tok.col) s;
        process_tokens tok true
    | _ ->
        close t.col weak_mode;
        Queue.add t.t waiting_tokens
  in
  let t = Lexer.gen_pretokens lexbuf in
  process_tokens t false

let next_token lexbuf =
  if Queue.is_empty waiting_tokens then process_tokens lexbuf;
  Queue.take waiting_tokens
