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
    | SLASH -> Format.fprintf ppf "/"
    | SEMICOLON -> Format.fprintf ppf ";"
    | RPAR -> Format.fprintf ppf ")"
    | RARROW -> Format.fprintf ppf "->"
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
    | EQUAL -> Format.fprintf ppf "=="
    | EQRARROW -> Format.fprintf ppf "=>"
    | EOF -> Format.fprintf ppf "#"
    | ELSE -> Format.fprintf ppf "else"
    | DOUBLECOLON -> Format.fprintf ppf "::"
    | DO -> Format.fprintf ppf "do"
    | DATA -> Format.fprintf ppf "data"
    | CONCAT -> Format.fprintf ppf "<>"
    | CLASS -> Format.fprintf ppf "class"
    | CASE -> Format.fprintf ppf "case"
    | AST -> Format.fprintf ppf "*"
    | UINDENT s -> Format.fprintf ppf "uindent(%s)" s
    | STR_CST s -> Format.fprintf ppf "str_cst(%s)" s
    | LINDENT s -> Format.fprintf ppf "lindent(%s)" s
    | INT_CST i -> Format.fprintf ppf "int_cst(%i)" i)

let pp_pretoken ppf pre_tok =
  PostLexer.(
    Format.fprintf ppf "{t = %a; col = %i}" pp_token pre_tok.t pre_tok.col)

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
