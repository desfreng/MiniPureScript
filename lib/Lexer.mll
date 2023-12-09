{
open Parser

type pretoken = { t : token; col : int }

exception LexingError of string * Lexing.position
(** Excpetion throw on lexing error *)

let illegal_char c lexbuf =
  let txt =
    Format.sprintf "Illegal character '%c' (code: %#x)." c (Char.code c)
  in
  raise (LexingError (txt, Lexing.lexeme_start_p lexbuf))

let too_large_int int_str lexbuf =
  let txt = Format.sprintf "Integer constant too large '%s'." int_str in
  raise (LexingError (txt, Lexing.lexeme_start_p lexbuf))

let illegal_str_lf lexbuf =
  raise
    (LexingError ("Illegal line feed in string.", Lexing.lexeme_start_p lexbuf))

let unterminated_str lexbuf =
  raise
    (LexingError
       ("Non terminating string definition.", Lexing.lexeme_start_p lexbuf))

let unterminated_str_gap lexbuf =
  raise
    (LexingError ("Non terminating string gap.", Lexing.lexeme_start_p lexbuf))

let illegal_char_gap c lexbuf =
  let txt =
    Format.sprintf "Illegal character in string gap '%c' (code: %#x).@." c
      (Char.code c)
  in
  raise (LexingError (txt, Lexing.lexeme_start_p lexbuf))

(** Compute the current column of the lexing buffer *)
let col lexbuf =
  let beg_pos = Lexing.lexeme_start_p lexbuf in
  beg_pos.pos_cnum - beg_pos.pos_bol

(** A function to convert any lindent in keyword if necessary *)
let find_keyword =
  let kw_tbl = Hashtbl.create 17 in
  List.iter
    (fun (s, t) -> Hashtbl.add kw_tbl s t)
    [
      ("case", CASE);
      ("class", CLASS);
      ("data", DATA);
      ("do", DO);
      ("else", ELSE);
      ("false", FALSE);
      ("forall", FORALL);
      ("if", IF);
      ("import", IMPORT);
      ("in", IN);
      ("instance", INSTANCE);
      ("let", LET);
      ("module", MODULE);
      ("of", OF);
      ("then", THEN);
      ("true", TRUE);
      ("where", WHERE);
    ];
  fun s lexbuf ->
  let t = try Hashtbl.find kw_tbl s with Not_found -> LINDENT s in
  { t; col = col lexbuf }


(** We store string constant in there *)
let str_buf = Buffer.create 1024

}

let digit = ['0'-'9']
let lower = ['a'-'z'] | '_'
let upper = ['A'-'Z']
let other = lower | upper | digit | '\''
let lindent = lower other*
let uindent = upper (other | '.')*
let integer = '0' | ['1'-'9'] digit*

rule gen_pretokens = parse
  | '\n'            { Lexing.new_line lexbuf; gen_pretokens lexbuf }
  | ' ' | '\t'      { gen_pretokens lexbuf }
  | eof             { { t = EOF; col = -1 } }

  | lindent as s    { find_keyword s lexbuf }
  | uindent as s    { { t = UINDENT s; col = col lexbuf } }
  | integer as s    { let col = col lexbuf in
                      let i = match int_of_string_opt s with
                              | Some i -> i
                              | None -> too_large_int s lexbuf
                      in { t = INT_CST i; col } }

  | '"'             { let col = col lexbuf in
                      let s = string_cst lexbuf in
                      { t = STR_CST s; col } }

  (* Expressions *)
  | "("             { { t = LPAR; col = col lexbuf } }
  | ")"             { { t = RPAR; col = col lexbuf } }
  | "="             { { t = EQ_SIGN; col = col lexbuf } }

  (* Operators *)
  | "=="            { { t = EQ; col = col lexbuf } }
  | "/="            { { t = NOT_EQ; col = col lexbuf } }
  | '<'             { { t = LT; col = col lexbuf } }
  | "<="            { { t = LE; col = col lexbuf } }
  | '>'             { { t = GT; col = col lexbuf } }
  | ">="            { { t = GE; col = col lexbuf } }
  | '+'             { { t = PLUS; col = col lexbuf } }
  | '-'             { { t = MINUS; col = col lexbuf } }
  | '*'             { { t = MUL; col = col lexbuf } }
  | '/'             { { t = DIV; col = col lexbuf } }
  | "<>"            { { t = CONCAT; col = col lexbuf } }
  | "&&"            { { t = AND; col = col lexbuf } }
  | "||"            { { t = OR; col = col lexbuf } }

  (* Typing *)
  | "->"            { { t = ARROW; col = col lexbuf } }
  | "=>"            { { t = EQRARROW; col = col lexbuf } }
  | "::"            { { t = DOUBLECOLON; col = col lexbuf } }
  | '.'             { { t = PERIOD; col = col lexbuf } }
  | ','             { { t = COMMA; col = col lexbuf } }
  | '|'             { { t = PIPE; col = col lexbuf } }

  (* Comments *)
  | "{-"            { multi_line_comment lexbuf; gen_pretokens lexbuf }
  | "--"            { single_line_comment lexbuf; gen_pretokens lexbuf }

  (* Unexpected ! *)
  | _ as c          { illegal_char c lexbuf }

and multi_line_comment = parse
| '\n'              { Lexing.new_line lexbuf; multi_line_comment lexbuf }
| "-}"              { () }
| eof               { () } (* To mimic the comportment of PureScript *)
| _                 { multi_line_comment lexbuf }

and single_line_comment = parse
| '\n'              { Lexing.new_line lexbuf }
| _                 { single_line_comment lexbuf }
| eof               { () }

and string_cst = parse
| "\\\""            { Buffer.add_char str_buf '"'; string_cst lexbuf  }
| "\\\\"            { Buffer.add_char str_buf '\\'; string_cst lexbuf  }
| "\\n"             { Buffer.add_char str_buf '\n'; string_cst lexbuf }
    (* To mimic the comportment of PureScript: *)
| '\n'              { illegal_str_lf lexbuf }
| '\\'              { string_gap lexbuf; string_cst lexbuf }
| '"'               { let s = Buffer.contents str_buf in
                      Buffer.clear str_buf; s }
| eof               { unterminated_str lexbuf }
| _ as c            { Buffer.add_char str_buf c; string_cst lexbuf }

and string_gap = parse
| '\n'              { Lexing.new_line lexbuf; string_gap lexbuf }
| '\t' | ' '        { string_gap lexbuf }
| '\\'              { () }
| eof               { unterminated_str_gap lexbuf }
| _ as c            { illegal_char_gap c lexbuf }

{ }
