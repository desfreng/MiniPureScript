let pp_error_head ppf
    ((beg_pos, end_pos) : Lexing.position * Lexing.position option) =
  let begin_col = beg_pos.pos_cnum - beg_pos.pos_bol in
  let end_col =
    match end_pos with
    | Some pos -> pos.pos_cnum - pos.pos_bol
    | None -> begin_col + 1
  in
  Format.fprintf ppf "File \"%s\", line %i, characters %i-%i:@."
    beg_pos.pos_fname beg_pos.pos_lnum begin_col end_col

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

let pp_pretoken ppf (pre_tok : Lexer.pretoken) =
  Format.fprintf ppf "{t = %a; col = %i}" pp_token pre_tok.t pre_tok.col

let pp_lexing_error ppf (err_type, loc) =
  pp_error_head ppf (loc, None);
  Lexer.(
    match err_type with
    | IllegalCharacter c ->
        Format.fprintf ppf "Illegal character '%c' (code: %#x).@." c
          (Char.code c)
    | TooLargeInteger s ->
        Format.fprintf ppf "Integer constant too large '%s'.@." s
    | IllegalLineFeedInString ->
        Format.fprintf ppf "Illegal line feed in string@."
    | UnterminatedString ->
        Format.fprintf ppf "Non terminating string definition@."
    | UnterminatedStringGap -> Format.fprintf ppf "Non terminating string gap@."
    | IllegalCharacterInGap c ->
        Format.fprintf ppf "Illegal character in string gap '%c' (code: %#x).@."
          c (Char.code c))

let pp_parsing_error ppf (tt, et, bp, ep) =
  pp_error_head ppf (bp, Some ep);
  Format.fprintf ppf "Unexpected text : '%s'. Expected : '%s'" tt et

let rec pp_ast_typ ppf t =
  Ast.(
    match t.v with
    | AstTVar s -> Format.pp_print_string ppf s
    | AstTData (d, args) ->
        Format.pp_print_string ppf d;
        List.iter (Format.fprintf ppf " (%a)" pp_ast_typ) args)

let pp_ttyp ppf t = Format.pp_print_string ppf (TAst.string_of_ttyp t)

let pp_tconst ppf c =
  TAst.(
    match c with
    | TConstUnit -> Format.pp_print_string ppf "unit"
    | TConstBool true -> Format.pp_print_string ppf "true"
    | TConstBool false -> Format.pp_print_string ppf "false"
    | TConstInt i -> Format.pp_print_int ppf i
    | TConstString s -> Format.pp_print_string ppf s)

let pp_ast_const ppf c =
  Ast.(
    match c.v with
    | True -> Format.pp_print_string ppf "true"
    | False -> Format.pp_print_string ppf "false"
    | Int i -> Format.pp_print_int ppf i
    | Str s -> Format.pp_print_string ppf s)

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

let rec pp_texpr ppf e =
  let rec print_expr_k ppf expr =
    TAst.(
      match expr with
      | TConstant c -> pp_tconst ppf c
      | TVariable i -> Format.pp_print_string ppf (VarId.name i)
      | TBinOp (lhs, op, rhs) ->
          Format.fprintf ppf "(%a) %a (%a)" pp_texpr lhs pp_binop op pp_texpr
            rhs
      | TApp (f, args) ->
          Format.pp_print_string ppf f;
          List.iter (Format.fprintf ppf " (%a)" pp_texpr) args
      | TConstructor (s, args) ->
          Format.fprintf ppf "(%a).(%s)" pp_ttyp e.expr_typ (ConstId.name s);
          List.iter (Format.fprintf ppf " (%a)" pp_texpr) args
      | TIf (c, t, f) ->
          Format.fprintf ppf
            "if (%a) then@.@[<hov 2>%a@]@.else@.@[<hov 2>%a@]@." pp_texpr c
            pp_texpr t pp_texpr f
      | TBlock l ->
          Format.fprintf ppf "@.@[<hov 2>";
          List.iter (Format.fprintf ppf "%a@." pp_texpr) l;
          Format.fprintf ppf "@]"
      | TLet (v_id, v_expr, expr) ->
          Format.fprintf ppf "let %s = (%a) in@;@[<v 2>%a@]" (VarId.name v_id)
            pp_texpr v_expr print_expr_k expr
      | _ -> assert false (* TODO *))
  in
  Format.fprintf ppf "(%a)::%a" print_expr_k e.expr pp_ttyp e.expr_typ

let rec pp_ast_expr ppf expr =
  Ast.(
    match expr.v with
    | ExprConst c -> pp_ast_const ppf c
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
