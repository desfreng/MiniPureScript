open TAst

type kind = Expression | Pattern

type type_error_kind =
  | UnknownTypeVar of string
  | UnknownSymbolType of string
  | SymbolArityMismatch of { typ : string; found : int; expected : int }
  | InvalidAnonymous
  | UndeclaredVariable of string
  | ExpectedTypeIn of { found : string; expected : string list }
  | NotSameSymbol of {
      kind : kind;
      t1 : string;
      t2 : string;
      symb1 : string;
          (** The symbol name in t1 that differ from the one in t2 *)
      symb2 : string;
          (** The symbol name in t2 that differ from the one in t1 *)
    }
  | NotSameType of {
      kind : kind;
      t1 : string;
      t2 : string;
      diff_t1 : string;  (** Part of t1 that differ from t2 *)
      diff_t2 : string;  (** Part of t2 that differ from t1 *)
    }
  | VariableOccuring of {
      kind : kind;
      t1 : string;
      t2 : string;
      var_name : string;
          (** The variable of one type which appears in a part of the other type *)
      typ : string;
          (** The part of one of the types in which the variable appears *)
    }
  | ConstructorArityMismatch of {
      kind : kind;
      const : string;
      found : int;
      expected : int;
    }
  | UnknownConstructor of { kind : kind; cst_name : string }
  | MultipleBindingsInPattern of string
  | VariableNotFunction of {
      var_name : string;
      var_typ : string;
      expected_arity : int;
    }
  | FunctionArityMismatch of { fn : string; found : int; expected : int }
  | UnknownFunction of string

exception TypeError of type_error_kind * Lexing.position * Lexing.position

(** The type variable is not in the current local env *)
let unknown_type_var n (pos : Ast.typ) =
  raise (TypeError (UnknownTypeVar n, pos.beg_pos, pos.end_pos))

(** This symbol type is not in the global env *)
let unknown_symbol_type n (pos : Ast.typ) =
  raise (TypeError (UnknownSymbolType n, pos.beg_pos, pos.end_pos))

(** There is a mismatch between the arity expected and found for a symbol type *)
let symbol_arity_mismatch decl ar_found (pos : Ast.typ) =
  raise
    (TypeError
       ( SymbolArityMismatch
           { typ = decl.symbid; found = ar_found; expected = decl.arity },
         pos.beg_pos,
         pos.end_pos ))

(** An anonymous argument '_' is used as an expression. *)
let invalid_anonymous (pos : Ast.expr) =
  raise (TypeError (InvalidAnonymous, pos.beg_pos, pos.end_pos))

(** The variable [n] is not declared. *)
let variable_not_declared n (pos : Ast.expr) =
  raise (TypeError (UndeclaredVariable n, pos.beg_pos, pos.end_pos))

(** The type found does not correspond to one of those we might have expected. *)
let expected_type_in found expected_list (pos : Ast.expr) =
  raise
    (TypeError
       ( ExpectedTypeIn
           {
             found = string_of_ttyp found;
             expected = List.map string_of_ttyp expected_list;
           },
         pos.beg_pos,
         pos.end_pos ))

(** An error occured during the unification of [t1] and [t2]. *)
let _unification_error kind err t1 t2 (pos : 'a Ast.pos) =
  match err with
  | SymbolMismatch s ->
      raise
        (TypeError
           ( NotSameSymbol
               {
                 kind;
                 t1 = string_of_ttyp t1;
                 t2 = string_of_ttyp t2;
                 symb1 = s.symb1;
                 symb2 = s.symb2;
               },
             pos.beg_pos,
             pos.end_pos ))
  | VariableOccuring v ->
      raise
        (TypeError
           ( VariableOccuring
               {
                 kind;
                 t1 = string_of_ttyp t1;
                 t2 = string_of_ttyp t2;
                 var_name = string_of_ttyp v.var;
                 typ = string_of_ttyp v.typ;
               },
             pos.beg_pos,
             pos.end_pos ))
  | NotSameTypes t ->
      raise
        (TypeError
           ( NotSameType
               {
                 kind;
                 t1 = string_of_ttyp t1;
                 t2 = string_of_ttyp t2;
                 diff_t1 = string_of_ttyp t.t1;
                 diff_t2 = string_of_ttyp t.t2;
               },
             pos.beg_pos,
             pos.end_pos ))

let expr_unification_error err t1 t2 (pos : Ast.expr) =
  _unification_error Expression err t1 t2 pos

let pat_unification_error err t1 t2 (pos : Ast.pattern) =
  _unification_error Pattern err t1 t2 pos

(** There is a mismatch between the arity expected and found for the call of a
    constructor type *)
let _cst_arit_mismatch kind const expected found (pos : 'a Ast.pos) =
  raise
    (TypeError
       ( ConstructorArityMismatch { kind; const; found; expected },
         pos.beg_pos,
         pos.end_pos ))

let expr_const_arity_mismatch consts expected found (pos : Ast.expr) =
  _cst_arit_mismatch Expression consts expected found pos

let pat_const_arity_mismatch consts expected found (pos : Ast.pattern) =
  _cst_arit_mismatch Pattern consts expected found pos

(** The constructor [n] is not in the global env *)
let _ukn_const kind n (pos : 'a Ast.pos) =
  raise
    (TypeError
       (UnknownConstructor { kind; cst_name = n }, pos.beg_pos, pos.end_pos))

let expr_unknown_constructor n (pos : Ast.expr) = _ukn_const Expression n pos
let pat_unknown_constructor n (pos : Ast.pattern) = _ukn_const Pattern n pos

(** The variable [n] appear more than one time in the pattern *)
let same_variable_in_pat n (pos : Ast.pattern) =
  raise (TypeError (MultipleBindingsInPattern n, pos.beg_pos, pos.end_pos))

(* Previously variable [fn] of type [typ] is not a function.
   Expected arity was [arity] *)
let variable_not_a_function var_name typ ex_arity (pos : 'a Ast.pos) =
  raise
    (TypeError
       ( VariableNotFunction
           { var_name; var_typ = string_of_ttyp typ; expected_arity = ex_arity },
         pos.beg_pos,
         pos.end_pos ))

(** This function name is not in the global env *)
let unknown_function n (pos : 'a Ast.pos) =
  raise (TypeError (UnknownFunction n, pos.beg_pos, pos.end_pos))

(** There is a mismatch between the number of argument expected and found
    for the call of a function *)
let function_arity_mismatch fundecl found (pos : 'a Ast.pos) =
  raise
    (TypeError
       ( FunctionArityMismatch
           { fn = fundecl.funid; found; expected = fundecl.arity },
         pos.beg_pos,
         pos.end_pos ))
