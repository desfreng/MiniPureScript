let pp_option pp ppf = function
  | None -> Format.pp_print_string ppf "None"
  | Some x -> Format.fprintf ppf "Some %a" pp x

let rec pp_list pp ppf = function
  | [] -> assert false
  | [ x ] -> Format.fprintf ppf " %a ]" pp x
  | hd :: tl -> Format.fprintf ppf " %a ;%a" pp hd (pp_list pp) tl

let pp_list pp ppf = function
  | [] -> Format.pp_print_string ppf "[]"
  | [ x ] -> Format.fprintf ppf "[ %a ]" pp x
  | hd :: tl -> Format.fprintf ppf "[ %a ;%a" pp hd (pp_list pp) tl

(** Pretty Print Post-Lexer tokens *)
let pp_token ppf t =
  Parser.(
    match t with
    | AND -> Format.fprintf ppf "and"
    | WHERE -> Format.fprintf ppf "where"
    | TRUE -> Format.fprintf ppf "true"
    | THEN -> Format.fprintf ppf "then"
    | DIV -> Format.fprintf ppf "/"
    | SEMICOLON -> Format.fprintf ppf ";"
    | RPAR -> Format.fprintf ppf ")"
    | ARROW -> Format.fprintf ppf "->"
    | RACC -> Format.fprintf ppf "}"
    | PLUS -> Format.fprintf ppf "+"
    | PERIOD -> Format.fprintf ppf "."
    | COMMA -> Format.fprintf ppf ","
    | OR -> Format.fprintf ppf "||"
    | OF -> Format.fprintf ppf "of"
    | NOT_EQ -> Format.fprintf ppf "/="
    | MODULE -> Format.fprintf ppf "module"
    | MINUS -> Format.fprintf ppf "-"
    | LT -> Format.fprintf ppf "<"
    | LPAR -> Format.fprintf ppf "("
    | LET -> Format.fprintf ppf "let"
    | LE -> Format.fprintf ppf "<="
    | LACC -> Format.fprintf ppf "{"
    | INSTANCE -> Format.fprintf ppf "instance"
    | IN -> Format.fprintf ppf "in"
    | IMPORT -> Format.fprintf ppf "import"
    | IF -> Format.fprintf ppf "if"
    | GT -> Format.fprintf ppf ">"
    | GE -> Format.fprintf ppf ">="
    | FORALL -> Format.fprintf ppf "forall"
    | FALSE -> Format.fprintf ppf "false"
    | EQ_SIGN -> Format.fprintf ppf "="
    | EQ -> Format.fprintf ppf "=="
    | EQRARROW -> Format.fprintf ppf "=>"
    | EOF -> Format.fprintf ppf "#"
    | PIPE -> Format.fprintf ppf "|"
    | ELSE -> Format.fprintf ppf "else"
    | DOUBLECOLON -> Format.fprintf ppf "::"
    | DO -> Format.fprintf ppf "do"
    | DATA -> Format.fprintf ppf "data"
    | CONCAT -> Format.fprintf ppf "<>"
    | CLASS -> Format.fprintf ppf "class"
    | CASE -> Format.fprintf ppf "case"
    | MUL -> Format.fprintf ppf "*"
    | UINDENT s -> Format.fprintf ppf "uindent(%s)" s
    | STR_CST s -> Format.fprintf ppf "str_cst(%s)" s
    | LINDENT s -> Format.fprintf ppf "lindent(%s)" s
    | INT_CST i -> Format.fprintf ppf "int_cst(%i)" i)

(** Pretty Print Lexer pre-tokens (token and their column position) *)
let pp_pretoken ppf (pre_tok : Lexer.pretoken) =
  Format.fprintf ppf "{t = %a; col = %i}" pp_token pre_tok.t pre_tok.col

(** Ast printing *)

(** Pretty Print an Ast type *)
let rec pp_ast_typ ppf t =
  Ast.(
    match t.v with
    | AstTVar s -> Format.pp_print_string ppf s
    | AstTData (d, args) ->
        Format.pp_print_string ppf d;
        List.iter (Format.fprintf ppf " (%a)" pp_ast_typ) args)

(** Pretty Print an Ast Constant *)
let pp_ast_const ppf c =
  Ast.(
    match c.v with
    | True -> Format.pp_print_string ppf "true"
    | False -> Format.pp_print_string ppf "false"
    | Int i -> Format.pp_print_int ppf i
    | Str s -> Format.pp_print_string ppf s)

(** Pretty Print a Binary Operator *)
let pp_binop ppf op =
  Ast.(
    match op with
    | Eq -> Format.fprintf ppf "=="
    | Neq -> Format.fprintf ppf "/="
    | Gt -> Format.fprintf ppf ">"
    | Ge -> Format.fprintf ppf ">="
    | Lt -> Format.fprintf ppf "<"
    | Le -> Format.fprintf ppf "<="
    | Plus -> Format.fprintf ppf "+"
    | Minus -> Format.fprintf ppf "-"
    | Div -> Format.fprintf ppf "/"
    | Mul -> Format.fprintf ppf "*"
    | Concat -> Format.fprintf ppf "<>"
    | And -> Format.fprintf ppf "&&"
    | Or -> Format.fprintf ppf "||")

(** Pretty Print an Ast Expression *)
let rec pp_ast_expr ppf expr =
  Ast.(
    match expr.v with
    | ExprConstant c -> pp_ast_const ppf c
    | ExprVar s -> Format.pp_print_string ppf s
    | WithType (e, t) ->
        Format.fprintf ppf "(%a)::%a" pp_ast_expr e pp_ast_typ t
    | Neg e -> Format.fprintf ppf "-(%a)" pp_ast_expr e
    | BinOp (lhs, op, rhs) ->
        Format.fprintf ppf "(%a) %a (%a)" pp_ast_expr lhs pp_binop op
          pp_ast_expr rhs
    | Let (b, e) ->
        Format.fprintf ppf "let @[<v 2>";
        List.iter
          (fun (n, e) -> Format.fprintf ppf "@ %s := %a" n pp_ast_expr e)
          b;
        Format.fprintf ppf "@.in (%a)" pp_ast_expr e
    | _ -> assert false)

(** TAst printing *)

(** Pretty Print TAst type *)
let pp_tast_ttyp ppf t =
  Format.pp_print_string ppf
    (ignore t;
     assert false)

(** Pretty Print an TAst Constant *)
let pp_tast_tconst ppf c =
  TAst.(
    match c with
    | TUnitConstant -> Format.pp_print_string ppf "unit"
    | TBoolConstant true -> Format.pp_print_string ppf "true"
    | TBoolConstant false -> Format.pp_print_string ppf "false"
    | TIntConstant i -> Format.pp_print_int ppf i
    | TStringConstant s -> Format.pp_print_string ppf s)

(** Pretty Print an TAst Expression *)
let pp_tast_texpr ppf e =
  let rec pp ppf expr =
    TAst.(
      match expr.expr with
      | TConstant c -> pp_tast_tconst ppf c
      | TVariable i ->
          Format.pp_print_string ppf
            (ignore i;
             assert false)
      | TBinOp (lhs, op, rhs) ->
          Format.fprintf ppf "(%a) %a (%a)" pp lhs pp_binop op pp rhs
      | TApp (f, args) ->
          Format.pp_print_string ppf f;
          List.iter (Format.fprintf ppf " (%a)" pp) args
      | TConstructor (s, args) ->
          Format.fprintf ppf "(%a).(%s)" pp_tast_ttyp e.expr_typ s;
          List.iter (Format.fprintf ppf " (%a)" pp) args
      | TIf (c, t, f) ->
          Format.fprintf ppf
            "if (%a) then@.@[<hov 2>%a@]@.else@.@[<hov 2>%a@]@." pp c pp t pp f
      | TBlock l ->
          Format.fprintf ppf "@.@[<hov 2>";
          List.iter (Format.fprintf ppf "%a@;" pp) l;
          Format.fprintf ppf "@]"
      | TLet (v_id, v_expr, expr) ->
          Format.fprintf ppf "let %s = (%a) in@;@[<v 2>%a@]"
            (ignore v_id;
             assert false)
            pp v_expr pp expr
      | TGetField (e, i) -> Format.fprintf ppf "Field(%a, %i)" pp e i
      | TContructorCase (e, m, o) ->
          Format.fprintf ppf "case (%a) in@[<v 2>" pp e;
          PatConstrMap.iter
            (fun cstr e ->
              match cstr with
              | TConstantConstr s ->
                  Format.fprintf ppf "@ %a -> %a@;" pp_tast_tconst s pp e
              | TSymbolConstr c -> Format.fprintf ppf "@ %s -> %a@;" c pp e)
            m;
          (match o with
          | Some e -> Format.fprintf ppf "@ otherwise -> %a" pp e
          | None -> ());
          Format.fprintf ppf "@]")
  in
  Format.fprintf ppf "(%a)::%a" pp e pp_tast_ttyp e.expr_typ

(** Pretty Print an TAst Pattern *)
let pp_tast_pat ppf p =
  let rec pp ppf p =
    TAst.(
      match p.pat with
      | TPatConstant c -> pp_tast_tconst ppf c
      | TPatWildcard -> Format.pp_print_string ppf "_"
      | TPatVar c ->
          Format.pp_print_string ppf
            (ignore c;
             assert false)
      | TPatConstructor (s, args) ->
          Format.fprintf ppf "(%a).(%s)" pp_tast_ttyp p.pat_typ s;
          List.iter (Format.fprintf ppf " (%a)" pp) args)
  in
  Format.fprintf ppf "(%a)::%a" pp p pp_tast_ttyp p.pat_typ
