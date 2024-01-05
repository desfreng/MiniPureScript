type position =
  {beg_line: int; beg_col: int; end_line: int; end_col: int; file: string}

type 'a pos = {v: 'a; pos: position}

type typ = typ_kind pos

and typ_kind = AstTVar of string | AstTData of string * typ list

type coi_decl = coi_decl_kind pos

and coi_decl_kind = CoI_Decl of string * typ list

type binop =
  | Eq
  | Neq
  | Gt
  | Ge
  | Lt
  | Le
  | Plus
  | Minus
  | Mul
  | Div
  | Concat
  | And
  | Or

type constant = constant_kind pos

and constant_kind = Int of int | Str of string | True | False

type expr = expr_kind pos

and expr_kind =
  | ExprConstant of constant (* constant *)
  | ExprVar of string (* A variable value *)
  | WithType of expr * typ (* annoted expression *)
  | Neg of expr (* Unary negation *)
  | BinOp of expr * binop * expr (* binary op *)
  | AppFun of string (* Function name *) * expr list (* args of function call *)
  | AppConstr of
      string (* Constructor name *) * expr list (* args of constructor call *)
  | If of expr * expr * expr (* if expression *)
  | Block of expr list (* block of multiple expression *)
  | Let of (string * expr) list * expr (* let (multiple bindings) in expr *)
  | Case of
      expr * (pattern * expr) list (* match of expr with list of pattern *)

and pattern = pattern_kind pos

and pattern_kind =
  | PatConstant of constant (* Constant *)
  | PatVariable of string (* A variable (in lowercase) *)
  | PatConstructor of string * pattern list (* A constructor *)

type decl = decl_kind pos

and decl_kind =
  | FunDecl of string (* fun name *) * pattern list (* args *) * expr (* expr *)
  | TypeDecl of
      string (* fun name *)
      * string list (* quantified var *)
      * coi_decl list (* class name used *)
      * typ list (* args type *)
      * typ (* return type *)
  | Data of
      string (* data name *)
      * string list (* data args *)
      * (string * typ list) list (* list of (Construtor Name, Args type list) *)
  | Class of
      string (* class name *)
      * string list (* class args *)
      * decl list (* list of type decls *)
  | Instance of
      (coi_decl list (* inst required *) * coi_decl (* instance *))
      * decl list (* fun decl list *)

type program = decl list

let lexloc_to_pos (pos : Lexing.position * Lexing.position) =
  let beg_p, end_p = pos in
  let file = beg_p.pos_fname in
  let beg_col = beg_p.pos_cnum - beg_p.pos_bol in
  let end_col = end_p.pos_cnum - end_p.pos_bol in
  {beg_line= beg_p.pos_lnum; beg_col; end_line= end_p.pos_lnum; end_col; file}

let lexbuf_to_pos lexbuf =
  lexloc_to_pos (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)

let merge_pos p1 p2 = {p1 with end_line= p2.end_line; end_col= p2.end_col}

let eof_pos lexbuf =
  let pos = lexbuf_to_pos lexbuf in
  {pos with end_col= -1; beg_col= -1}

exception UnexpectedText of string * position

let assert_text_is (token_text, pos) text =
  if token_text <> text then
    raise
      (UnexpectedText
         ( Format.sprintf "Unexpected text : '%s'. Expected : '%s'" token_text
             text
         , pos ) )
