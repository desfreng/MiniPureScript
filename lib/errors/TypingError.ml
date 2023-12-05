open TAst

type decl_type = Symbol | Class | Function | Constructor

type type_error_kind =
  | UnknownTypeVar of string
  | UnknownDecl of { decl_name : string; decl_type : decl_type }
  | ArityMismatch of {
      decl_name : string;
      decl_type : decl_type;
      found : int;
      expected : int;
    }
  | InvalidAnonymous
  | UnknownVariable of string
  | ExpectedTypeIn of { found : string; expected : string list }
  | NotSameSymbol of {
      t1 : string;
      t2 : string;
      symb1 : string;
          (** The symbol name in t1 that differ from the one in t2 *)
      symb2 : string;
          (** The symbol name in t2 that differ from the one in t1 *)
    }
  | NotSameType of {
      t1 : string;
      t2 : string;
      diff_t1 : string;  (** Part of t1 that differ from t2 *)
      diff_t2 : string;  (** Part of t2 that differ from t1 *)
    }
  | VariableOccuring of {
      t1 : string;
      t2 : string;
      var_name : string;
          (** The variable of one type which appears in a part of the other type *)
      typ : string;
          (** The part of one of the types in which the variable appears *)
    }
  | MultipleBindingsInPattern of string
  | VariableNotFunction of {
      var_name : string;
      var_typ : string;
      expected_arity : int;
    }
  | UnresolvedInstance of string
  | TypeVarAlreadyDeclared of {
      var : string;
      decl_type : decl_type;
      decl_name : string;
    }
  | DeclAlreadyDeclared of { decl_name : string; decl_type : decl_type }
  | ConstructorAlreadyInSymbol of { constr : string; symbol : string }
  | ConstructorAlreadyInGEnv of {
      constr : string;
      symbol : string;
      decl_symbol : string;
    }
  | QuantifiedVarInDeclFunClass of { fun_name : string; class_name : string }
  | InstanceInDeclFunClass of { fun_name : string; class_name : string }
  | MissingFunctionTypeDecl of string
  | MultipleBindingsInFuntion of { var_name : string; fun_name : string }
  | MultipleNonVarPatternInFuntion
  | StrangeNonVarPlacement of string
  | MissingFunImpl of string
  | NotExhaustiveCase
  | NotExhaustiveFun of string
  | MultipleFunDef of string
  | MissingMain
  | SameFunInClass of { fun_name : string; class_name : string }
  | CanUnifyInst of {
      existing_inst : string * string list;
      new_inst : string * string list;
    }
  | FunAlreadyDefInInstance of string
  | FunNotInClass of { fname : string; class_name : string }
  | FunUndefinedInInstance of string list

exception TypeError of type_error_kind * Lexing.position * Lexing.position

(** The type variable is not in the current local env *)
let unknown_type_var n (pos : Ast.typ) =
  raise (TypeError (UnknownTypeVar n, pos.beg_pos, pos.end_pos))

(** This symbol type is not in the global env *)
let unknown_symbol n (pos : Ast.typ) =
  raise
    (TypeError
       ( UnknownDecl { decl_name = n; decl_type = Symbol },
         pos.beg_pos,
         pos.end_pos ))

(** There is a mismatch between the arity expected and found for a symbol type *)
let symbol_arity_mismatch decl ar_found (pos : Ast.typ) =
  raise
    (TypeError
       ( ArityMismatch
           {
             decl_name = decl.symbid;
             decl_type = Symbol;
             found = ar_found;
             expected = decl.arity;
           },
         pos.beg_pos,
         pos.end_pos ))

(** An anonymous argument '_' is used as an expression. *)
let invalid_anonymous (pos : Ast.expr) =
  raise (TypeError (InvalidAnonymous, pos.beg_pos, pos.end_pos))

(** The variable [n] is not declared. *)
let variable_not_declared n (pos : Ast.expr) =
  raise (TypeError (UnknownVariable n, pos.beg_pos, pos.end_pos))

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
let unification_error err t1 t2 (pos : 'a Ast.pos) =
  match err with
  | SymbolMismatch s ->
      raise
        (TypeError
           ( NotSameSymbol
               {
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
                 t1 = string_of_ttyp t1;
                 t2 = string_of_ttyp t2;
                 diff_t1 = string_of_ttyp t.t1;
                 diff_t2 = string_of_ttyp t.t2;
               },
             pos.beg_pos,
             pos.end_pos ))

(** There is a mismatch between the arity expected and found for the call of a
    constructor type *)
let constr_arity_mismatch constr expected found (pos : 'a Ast.pos) =
  raise
    (TypeError
       ( ArityMismatch
           { decl_name = constr; decl_type = Constructor; found; expected },
         pos.beg_pos,
         pos.end_pos ))

(** The constructor [n] is not in the global env *)
let unknown_constructor n (pos : 'a Ast.pos) =
  raise
    (TypeError
       ( UnknownDecl { decl_name = n; decl_type = Constructor },
         pos.beg_pos,
         pos.end_pos ))

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
  raise
    (TypeError
       ( UnknownDecl { decl_name = n; decl_type = Function },
         pos.beg_pos,
         pos.end_pos ))

(** There is a mismatch between the number of argument expected and found
    for the call of a function *)
let function_arity_mismatch fname expected found (pos : 'a Ast.pos) =
  raise
    (TypeError
       ( ArityMismatch
           { decl_name = fname; found; expected; decl_type = Function },
         pos.beg_pos,
         pos.end_pos ))

(** An instance was needed to perform a function call and it cannot be resolved *)
let unresolved_instance inst (pos : Ast.expr) =
  let (TInstance (cls_name, inst_ttyp)) = inst in
  raise
    (TypeError
       ( UnresolvedInstance
           (List.fold_left
              (fun acc typ -> acc ^ " " ^ string_of_ttyp typ)
              cls_name inst_ttyp),
         pos.beg_pos,
         pos.end_pos ))

(** The type variable [var] is already declared in the symbol type [symbol] *)
let typ_var_already_decl_in_symb var symbol (pos : Ast.decl) =
  raise
    (TypeError
       ( TypeVarAlreadyDeclared { var; decl_name = symbol; decl_type = Symbol },
         pos.beg_pos,
         pos.end_pos ))

(** The symbol [symbol] already exists in the global environement *)
let symbol_already_exists symbol (pos : Ast.decl) =
  raise
    (TypeError
       ( DeclAlreadyDeclared { decl_name = symbol; decl_type = Symbol },
         pos.beg_pos,
         pos.end_pos ))

(** The constructor [constr] is already declared in the symbol type [symbol] *)
let constr_already_in_symb constr symbol (pos : Ast.decl) =
  raise
    (TypeError
       (ConstructorAlreadyInSymbol { constr; symbol }, pos.beg_pos, pos.end_pos))

(** The constructor [constr] of the symbol type [symdecl] is already declared in
    the global environment, in the symbol [decl] *)
let constr_already_in_genv constr symdecl decl (pos : Ast.decl) =
  let symbol = symdecl.symbid in
  let decl_symbol = decl.symbid in
  raise
    (TypeError
       ( ConstructorAlreadyInGEnv { constr; symbol; decl_symbol },
         pos.beg_pos,
         pos.end_pos ))

(** The function [fun_name] already exists in the global environement *)
let function_already_exists fun_name (pos : Ast.decl) =
  raise
    (TypeError
       ( DeclAlreadyDeclared { decl_name = fun_name; decl_type = Function },
         pos.beg_pos,
         pos.end_pos ))

(** The symbol [symbol] already exists in the global environement *)
let class_already_exists class_name (pos : Ast.decl) =
  raise
    (TypeError
       ( DeclAlreadyDeclared { decl_name = class_name; decl_type = Class },
         pos.beg_pos,
         pos.end_pos ))

(** The type variable [var] is already declared in the class [class_name] *)
let typ_var_already_decl_in_class var class_name (pos : Ast.decl) =
  raise
    (TypeError
       ( TypeVarAlreadyDeclared
           { var; decl_name = class_name; decl_type = Class },
         pos.beg_pos,
         pos.end_pos ))

(** In the class declaration [class_name] the function [fname] has quantified
    variable *)
let no_qvar_in_class_fun_decl fun_name class_name (pos : Ast.decl) =
  raise
    (TypeError
       ( QuantifiedVarInDeclFunClass { fun_name; class_name },
         pos.beg_pos,
         pos.end_pos ))

(** In the class declaration [class_name] the function [fname] has instances
    required. *)
let no_instl_in_class_fun_decl fun_name class_name (pos : Ast.decl) =
  raise
    (TypeError
       ( InstanceInDeclFunClass { fun_name; class_name },
         pos.beg_pos,
         pos.end_pos ))

(** We missed the type declaration of the function [fun_name] *)
let missing_fun_type_decl fun_name (pos : Ast.decl) =
  raise (TypeError (MissingFunctionTypeDecl fun_name, pos.beg_pos, pos.end_pos))

(** The type variable [var] is already declared in the function [fun_name] *)
let typ_var_already_decl_in_fun var fun_name (pos : Ast.decl) =
  raise
    (TypeError
       ( TypeVarAlreadyDeclared
           { var; decl_name = fun_name; decl_type = Function },
         pos.beg_pos,
         pos.end_pos ))

(** This class is not in the global env *)
let unknown_class n (pos : 'a Ast.pos) =
  raise
    (TypeError
       ( UnknownDecl { decl_name = n; decl_type = Class },
         pos.beg_pos,
         pos.end_pos ))

let class_arity_mismatch class_decl ar_found (pos : Ast.coi_decl) =
  raise
    (TypeError
       ( ArityMismatch
           {
             decl_name = class_decl.class_name;
             decl_type = Class;
             expected = class_decl.carity;
             found = ar_found;
           },
         pos.beg_pos,
         pos.end_pos ))

(** The variable [n] appear more than one time in the funcion arguments *)
let same_variable_in_fun var_name fun_name (pos : Ast.pattern) =
  raise
    (TypeError
       ( MultipleBindingsInFuntion { var_name; fun_name },
         pos.beg_pos,
         pos.end_pos ))

let multiples_non_var_in_fun_args (pos : Ast.pattern) =
  raise (TypeError (MultipleNonVarPatternInFuntion, pos.beg_pos, pos.end_pos))

let strange_non_var_in_decls fun_name (pos : Ast.decl) =
  raise (TypeError (StrangeNonVarPlacement fun_name, pos.beg_pos, pos.end_pos))

let missing_fun_impl fun_name (pos : Ast.decl) =
  raise (TypeError (MissingFunImpl fun_name, pos.beg_pos, pos.end_pos))

let not_exhaustive_case (pos : Ast.expr) =
  raise (TypeError (NotExhaustiveCase, pos.beg_pos, pos.end_pos))

let not_exhaustive_fun fname (pos : Ast.decl list) =
  let fst = List.hd pos in
  let lst = List.rev pos |> List.hd in
  raise (TypeError (NotExhaustiveFun fname, fst.beg_pos, lst.end_pos))

let multiple_fun_def fname (pos : Ast.decl) =
  raise (TypeError (MultipleFunDef fname, pos.beg_pos, pos.end_pos))

let missing_main (pos : Ast.program) =
  let lst = List.rev pos |> List.hd in
  raise (TypeError (MissingMain, lst.beg_pos, lst.end_pos))

let same_fun_in_class fun_name class_name (pos : Ast.decl) =
  raise
    (TypeError
       (SameFunInClass { fun_name; class_name }, pos.beg_pos, pos.end_pos))

let can_unify_instances prod_inst sdecl (pos : Ast.decl) =
  let (TInstance (c_name, ttyps)) = prod_inst in
  let new_inst = (c_name, List.map string_of_ttyp ttyps) in
  let (TInstance (c_name, ttyps)) = sdecl.prod in
  let existing_inst = (c_name, List.map string_of_ttyp ttyps) in
  raise
    (TypeError
       (CanUnifyInst { new_inst; existing_inst }, pos.beg_pos, pos.end_pos))

let function_already_defined fname (pos : Ast.decl) =
  raise (TypeError (FunAlreadyDefInInstance fname, pos.beg_pos, pos.end_pos))

let function_not_in_class fname class_decl (pos : Ast.decl) =
  let class_name = class_decl.class_name in
  raise
    (TypeError (FunNotInClass { fname; class_name }, pos.beg_pos, pos.end_pos))

let missing_functions fdone class_decl (pos : Ast.decl) =
  let funlist =
    SMap.fold
      (fun x _ acc -> if SSet.mem x fdone then acc else x :: acc)
      class_decl.cfun_decls []
  in
  raise (TypeError (FunUndefinedInInstance funlist, pos.beg_pos, pos.end_pos))
