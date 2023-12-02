type 'a pos = { v : 'a; beg_pos : Lexing.position; end_pos : Lexing.position }

type typ = typ_kind pos
and typ_kind = AstTVar of string | AstTData of string * typ list

type binop =
  | Eq
  | Neq
  | Gt
  | Ge
  | Lt
  | Le
  | Plus
  | Minus
  | Div
  | Mul
  | Concat
  | And
  | Or

type constant = constant_kind pos
and constant_kind = Int of int | Str of string | True | False

type expr = expr_kind pos

and expr_kind =
  | ExprConst of constant (* constant *)
  | ExprVar of string (* A variable value *)
  | WithType of expr * typ (* annoted expression *)
  | Neg of expr (* Unary negation *)
  | BinOp of expr * binop * expr (* binary op *)
  | AppFun of string (* Function name *) * expr list (* args of function call *)
  | AppConst of
      string (* Constructor name *) * expr list (* args of constructor call *)
  | If of expr * expr * expr (* if expression *)
  | Block of expr list (* block of multiple expression *)
  | Let of (string * expr) list * expr (* let (multiple bindings) in expr *)
  | Case of
      expr * (pattern * expr) list (* match of expr with list of pattern *)

and pattern = pattern_kind pos

and pattern_kind =
  | PatConst of constant (* Constant *)
  | PatVar of string (* A variable (in lowercase) *)
  | PatConstructor of string * pattern list (* A constructor *)

type decl = decl_kind pos

and decl_kind =
  | FunDecl of string (* fun name *) * pattern list (* args *) * expr (* expr *)
  | TypeDecl of
      string (* fun name *)
      * string list (* quantified var *)
      * typ list (* class name used *)
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
      (typ (* class name implemented *) * typ list (* inst name *))
      * decl list (* fun decl list *)

type program = decl list
