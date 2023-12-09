{
open Tokens
open Ast

type pretoken = { t : token; pos : position }

exception LexingError of string * position
(** Exception throw on lexing error *)


let illegal_char c lexbuf =
  let txt =
    Format.sprintf "Illegal character '%c' (code: %#x)." c (Char.code c)
  in
  raise (LexingError (txt, lexbuf_to_pos lexbuf))

let too_large_int int_str lexbuf =
  let txt = Format.sprintf "Integer constant too large '%s'." int_str in
  raise (LexingError (txt, lexbuf_to_pos lexbuf))

let illegal_str_lf lexbuf =
  raise (LexingError ("Illegal line feed in string.", lexbuf_to_pos lexbuf))

let unterminated_str lexbuf =
  raise
    (LexingError ("Non terminating string definition.", lexbuf_to_pos lexbuf))

let unterminated_str_gap lexbuf =
  raise (LexingError ("Non terminating string gap.", lexbuf_to_pos lexbuf))

let illegal_char_gap c lexbuf =
  let txt =
    Format.sprintf "Illegal character in string gap '%c' (code: %#x).@." c
      (Char.code c)
  in
  raise (LexingError (txt, lexbuf_to_pos lexbuf))


let mk_pretok t lexbuf = { t; pos = lexbuf_to_pos lexbuf }

let mk_pretok_merge t beg_p end_p = { t; pos = merge_pos beg_p end_p }
let eof lexbuf = { t = EOF; pos = eof_pos lexbuf }


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
  mk_pretok t lexbuf


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
  | eof             { eof lexbuf }

  | lindent as s    { find_keyword s lexbuf }
  | uindent as s    { mk_pretok (UINDENT s) lexbuf }

  | integer as s    { let pos = lexbuf_to_pos lexbuf in
                      let i = match int_of_string_opt s with
                              | Some i -> i
                              | None -> too_large_int s lexbuf
                      in { t = INT_CST i; pos } }

  | '"'             { let beg_pos = lexbuf_to_pos lexbuf in
                      let s = string_cst lexbuf in
                      let end_pos = lexbuf_to_pos lexbuf in
                      mk_pretok_merge (STR_CST s) beg_pos end_pos }

  (* Expressions *)
  | "("             { mk_pretok LPAR lexbuf }
  | ")"             { mk_pretok RPAR lexbuf }
  | "="             { mk_pretok EQ_SIGN lexbuf }

  (* Operators *)
  | "=="            { mk_pretok EQ lexbuf }
  | "/="            { mk_pretok NOT_EQ lexbuf }
  | '<'             { mk_pretok LT lexbuf }
  | "<="            { mk_pretok LE lexbuf }
  | '>'             { mk_pretok GT lexbuf }
  | ">="            { mk_pretok GE lexbuf }
  | '+'             { mk_pretok PLUS lexbuf }
  | '-'             { mk_pretok MINUS lexbuf }
  | '*'             { mk_pretok MUL lexbuf }
  | '/'             { mk_pretok DIV lexbuf }
  | "<>"            { mk_pretok CONCAT lexbuf }
  | "&&"            { mk_pretok AND lexbuf }
  | "||"            { mk_pretok OR lexbuf }

  (* Typing *)
  | "->"            { mk_pretok ARROW lexbuf }
  | "=>"            { mk_pretok EQRARROW lexbuf }
  | "::"            { mk_pretok DOUBLECOLON lexbuf }
  | '.'             { mk_pretok PERIOD lexbuf }
  | ','             { mk_pretok COMMA lexbuf }
  | '|'             { mk_pretok PIPE lexbuf }

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
