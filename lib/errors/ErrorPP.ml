let _vscode_mode = true

let pp_error_head ppf
    ((beg_pos, end_pos) : Lexing.position * Lexing.position option) =
  let begin_col = beg_pos.pos_cnum - beg_pos.pos_bol in
  let end_col =
    match end_pos with
    | Some pos -> pos.pos_cnum - pos.pos_bol
    | None -> begin_col + 1
  in
  let begin_col, end_col =
    if _vscode_mode then (begin_col + 1, end_col + 1) else (begin_col, end_col)
  in
  Format.fprintf ppf "File \"%s\", line %i, characters %i-%i:@."
    beg_pos.pos_fname beg_pos.pos_lnum begin_col end_col

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

let rec _pp_list ppf = function
  | [] -> assert false
  | [ x ] -> Format.fprintf ppf " %s ]" x
  | hd :: tl -> Format.fprintf ppf " %s ;%a" hd _pp_list tl

let _pp_list ppf = function
  | [] -> Format.pp_print_string ppf "[]"
  | [ x ] -> Format.fprintf ppf "[ %s ]" x
  | hd :: tl -> Format.fprintf ppf "[ %s ;%a" hd _pp_list tl

let _pp_inst ppf (cn, typ) =
  Format.fprintf ppf "%s" cn;
  List.iter (Format.fprintf ppf " %s") typ

let pp_typing_error ppf (terr, bp, ep) =
  pp_error_head ppf (bp, Some ep);
  TypingError.(
    match terr with
    | UnknownTypeVar v ->
        Format.fprintf ppf
          "In this type annotation, the type variable '%s' is not defined." v
    | UnknownDecl v -> (
        match v.decl_type with
        | Symbol ->
            Format.fprintf ppf
              "In this type annotation, the symbol '%s' is not defined."
              v.decl_name
        | Class ->
            Format.fprintf ppf
              "In this type annotation, the class '%s' is not defined."
              v.decl_name
        | Function ->
            Format.fprintf ppf
              "In this expression, the function '%s' is not defined."
              v.decl_name
        | Constructor ->
            Format.fprintf ppf
              "In this expression, the constructor '%s' is not defined."
              v.decl_name)
    | ArityMismatch v -> (
        match v.decl_type with
        | Symbol ->
            Format.fprintf ppf "The symbol %s expected %i arguments but got %i."
              v.decl_name v.expected v.found
        | Class ->
            Format.fprintf ppf "The class %s expected %i arguments but got %i."
              v.decl_name v.expected v.found
        | Function ->
            Format.fprintf ppf
              "The function %s expected %i arguments but got %i." v.decl_name
              v.expected v.found
        | Constructor ->
            Format.fprintf ppf
              "The constructor %s expected %i arguments but got %i." v.decl_name
              v.expected v.found)
    | InvalidAnonymous ->
        Format.fprintf ppf "This expression cannot be used as a value."
    | UnknownVariable v ->
        Format.fprintf ppf
          "In this expression, the variable '%s' is not defined." v
    | ExpectedTypeIn v ->
        Format.fprintf ppf "We expected a type in %a but we got %s." _pp_list
          v.expected v.found
    | NotSameSymbol v ->
        Format.fprintf ppf
          "During the unification of the type %s with type %s,\n\
          \ we expected the symbol %s but we found the symbol %s." v.t1 v.t2
          v.symb1 v.symb2
    | NotSameType v ->
        Format.fprintf ppf
          "During the unification of the type %s with type %s,\n\
          \ we the type %s is not unifiable with the type %s." v.t1 v.t2
          v.diff_t1 v.diff_t2
    | VariableOccuring v ->
        Format.fprintf ppf
          "During the unification of the type %s with type %s,\n\
          \ the variable %s occurs in the type %s." v.t1 v.t2 v.var_name v.typ
    | MultipleBindingsInPattern v ->
        Format.fprintf ppf
          "In this pattern, the variable %s occurs multiple times." v
    | VariableNotFunction v ->
        Format.fprintf ppf
          "In this expression, the variable %s of type %s is not a function \
           with %i arguments."
          v.var_name v.var_typ v.expected_arity
    | UnresolvedInstance v ->
        Format.fprintf ppf
          "In this expression, the instance %s was needed, but it cant be \
           resolved with this environment."
          v
    | TypeVarAlreadyDeclared v -> (
        match v.decl_type with
        | Symbol ->
            Format.fprintf ppf
              "The type variable %s is declared multiples times as an argument \
               of the symbol %s."
              v.var v.decl_name
        | Class ->
            Format.fprintf ppf
              "The type variable %s is declared multiples times as an argument \
               of the class %s."
              v.var v.decl_name
        | Function ->
            Format.fprintf ppf
              "The type variable %s is declared multiples times as a \
               quantified variable of the function %s."
              v.var v.decl_name
        | Constructor -> assert false)
    | DeclAlreadyDeclared v -> (
        match v.decl_type with
        | Symbol ->
            Format.fprintf ppf "The symbol %s is already declared." v.decl_name
        | Class ->
            Format.fprintf ppf "The class %s is already declared." v.decl_name
        | Function ->
            Format.fprintf ppf "The function %s is already declared."
              v.decl_name
        | Constructor -> assert false)
    | ConstructorAlreadyInSymbol v ->
        Format.fprintf ppf
          "In the declaration of the symbol %s,\n\
          \ the constructor %s is declared multiples times." v.symbol v.constr
    | ConstructorAlreadyInGEnv v ->
        Format.fprintf ppf
          "In the declaration of the symbol %s,\n\
          \ the constructor %s is already declared in the symbol %s." v.symbol
          v.constr v.decl_symbol
    | QuantifiedVarInDeclFunClass v ->
        Format.fprintf ppf
          "In the declaration of the class %s,\n\
          \ the function %s has quantified variables." v.class_name v.fun_name
    | InstanceInDeclFunClass v ->
        Format.fprintf ppf
          "In the declaration of the class %s,\n\
          \ the function %s has required instances." v.class_name v.fun_name
    | MissingFunctionTypeDecl v ->
        Format.fprintf ppf "Missing type declaration of the function %s." v
    | MultipleBindingsInFuntion v ->
        Format.fprintf ppf
          "In this equation of the function %s, the variable %s is bound \
           multiple times. "
          v.fun_name v.var_name
    | MultipleNonVarPatternInFuntion ->
        Format.pp_print_string ppf
          "The pattern matching can only occurs on one argument of the \
           function."
    | StrangeNonVarPlacement v ->
        Format.fprintf ppf
          "The pattern matching can only occurs on the same argument of the \
           function %s."
          v
    | MissingFunImpl v ->
        Format.fprintf ppf
          "The declaration of the type of the function %s must be followed by \
           its definition."
          v
    | NotExhaustiveCase ->
        Format.pp_print_string ppf
          "Patterns of this case expression are not exhaustive."
    | NotExhaustiveFun v ->
        Format.fprintf ppf
          "The patterns in the argument of the function %s in not exhaustive." v
    | MultipleFunDef v ->
        Format.fprintf ppf "The function %s is already completly implemented." v
    | MissingMain ->
        Format.pp_print_string ppf
          "The function main is not declared nor implemented."
    | SameFunInClass v ->
        Format.fprintf ppf
          "The function %s is already declared in the class %s." v.fun_name
          v.class_name
    | CanUnifyInst v ->
        Format.fprintf ppf
          "The instance resolved %a can be unified with the instance %a \
           already present in the environment"
          _pp_inst v.new_inst _pp_inst v.existing_inst
    | FunAlreadyDefInInstance v ->
        Format.fprintf ppf
          "The function %s is already defined in this instance." v
    | FunNotInClass v ->
        Format.fprintf ppf "No declaration for the function %s in the class %s."
          v.fname v.class_name
    | FunUndefinedInInstance v ->
        Format.fprintf ppf
          "Missing the implementation of the functions %a in this instance."
          _pp_list v)
