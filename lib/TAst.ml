module type Id = sig
  type t

  val fresh : string option -> t
  val compare : t -> t -> int
  val name : t -> string
end

(** A module to manipulate unique id with name. *)
module IntId (E : sig
  val type_name : string
end) : Id = struct
  type t = int * string

  let fresh =
    let cpt = ref 0 in
    fun name ->
      incr cpt;
      ( !cpt,
        let nid = Format.asprintf "%s%i" E.type_name !cpt in
        match name with Some n -> n ^ "(" ^ nid ^ ")" | None -> nid )

  let compare (x, _) (y, _) = Stdlib.compare x y
  let name = snd
end

(** Id of a unified type variable. *)
module TVarId = IntId (struct
  let type_name = "'weak"
end)

module TVarMap = Map.Make (TVarId)
module SMap = Map.Make (String)
module SSet = Set.Make (String)

(** Type of an expression. *)
type ttyp =
  | TQuantifiedVar of string
  | TVar of { id : TVarId.t; mutable def : ttyp option }
  | TSymbol of string * ttyp list

(** [new_tvar ()] creates a fresh type variable, without any information about
    its value, nor its name. *)
let new_tvar () = TVar { id = TVarId.fresh None; def = None }

(** [unfold v] unfolds the "top-level" unifications oppered on a unified type variable
    Invariant: if the return is a TVar, def is None.*)
let rec unfold v = match v with TVar { def = Some t; _ } -> unfold t | _ -> v

(** [string_of_ttyp t] returns a string corresponding to the representation of [t] *)
let rec string_of_ttyp t =
  match unfold t with
  | TSymbol (s, args) ->
      List.fold_left (fun acc t -> acc ^ " " ^ string_of_ttyp t) s args
  | TVar { id; _ } -> TVarId.name id
  | TQuantifiedVar s -> s

(** [subst s t] applies the substitution [s] (that maps quantifed variable to
    type variables) to all variables in [t] *)
let rec subst s t =
  let t = unfold t in
  match t with
  | TVar _ -> t
  | TSymbol (sid, args) -> TSymbol (sid, List.map (subst s) args)
  | TQuantifiedVar n -> (
      match SMap.find_opt n s with Some t -> t | None -> t)

(** [occurs vid t] checks if the variable id [vid] occurs in the type [t]*)
let rec occurs vid t =
  match unfold t with
  | TSymbol (_, args) -> List.exists (occurs vid) args
  | TVar { id; _ } -> vid = id
  | TQuantifiedVar _ -> false

(** [lfresh_subst l] creates a substitution of quantified variables from the
    list [l] to fresh type variables. *)
let lfresh_subst =
  List.fold_left (fun acc v -> SMap.add v (new_tvar ()) acc) SMap.empty

(** [sfresh_subst s] creates a substitution of quantified variables from the
    set [s] to fresh type variables. *)
let sfresh_subst s =
  SSet.fold (fun v acc -> SMap.add v (new_tvar ()) acc) s SMap.empty

(** The structure carried by the exception *)
type unif_error =
  | SymbolMismatch of { symb1 : string; symb2 : string }
  | VariableOccuring of { var : ttyp; typ : ttyp }
  | NotSameTypes of { t1 : ttyp; t2 : ttyp }

exception UnificationError of unif_error
(** Exception thrown by [unify] *)

(** [unify t1 t2] attempts to find a substitution for the variables in [t1] and
    [t2] so that the two types are equal. If this process fails, a
    [UnificationError] is generated containing all the information indicating
    what has happened.
    @raise *)
let rec unify t1 t2 =
  let t1, t2 = (unfold t1, unfold t2) in
  match (t1, t2) with
  | TSymbol (sid1, args1), TSymbol (sid2, args2) ->
      if sid1 = sid2 then List.iter2 unify args1 args2
      else
        raise (UnificationError (SymbolMismatch { symb1 = sid1; symb2 = sid2 }))
  | TQuantifiedVar s1, TQuantifiedVar s2 ->
      if s1 = s2 then () else raise (UnificationError (NotSameTypes { t1; t2 }))
  | TVar v, t ->
      if occurs v.id t then
        raise (UnificationError (VariableOccuring { var = TVar v; typ = t }))
      else v.def <- Some t
  | _, TVar _ -> unify t2 t1
  | TSymbol _, TQuantifiedVar _ | TQuantifiedVar _, TSymbol _ ->
      raise (UnificationError (NotSameTypes { t1; t2 }))

(** [can_unify t1 t2] check if [t1] can be unified with [t2].
    Beware ! We modify the variables ! *)
let can_unify t1 t2 =
  try
    unify t1 t2;
    true
  with UnificationError _ -> false

(** [copy t] creates a copy of the type [t] *)
let rec copy t =
  match unfold t with
  | TVar _ -> TVar { id = TVarId.fresh None; def = None }
  | TQuantifiedVar s -> TQuantifiedVar s
  | TSymbol (s, args) -> TSymbol (s, List.map copy args)

(** Id of a variable. *)
module VarId = IntId (struct
  let type_name = "var"
end)

(** Id of a function. *)
module FunId = IntId (struct
  let type_name = "fun"
end)

(** A constant in the Typped AST *)
type tconst =
  | TUnitConstant
  | TBoolConstant of bool
  | TIntConstant of int
  | TStringConstant of string

(** A type to represent a "pattern constructor" in the TCompiledCase expression *)
type comp_pat_constr =
  | TSymbolConstr of string (* This is a symbol "pattern constructor" *)
  | TConstantConstr of tconst (* This is a constant "pattern constructor" *)

module CompPatConstr = struct
  type t = comp_pat_constr

  let compare = Stdlib.compare
end

module CompPatConstrMap = Map.Make (CompPatConstr)
module CompPatConstrSet = Set.Make (CompPatConstr)

type texpr = { expr : texpr_kind; expr_typ : ttyp }
(** Expression type *)

and texpr_kind =
  | TConstant of tconst
  | TVariable of VarId.t
  | TBinOp of texpr * Ast.binop * texpr
  | TApp of string * texpr list (* Function application *)
  | TConstructor of string * texpr list (* Constructor application *)
  | TIf of texpr * texpr * texpr
  | TBlock of texpr list
  | TLet of VarId.t * texpr * texpr
  | TContructorCase of
      texpr (* The expression for which we are looking at the constructor *)
      * texpr CompPatConstrMap.t
      (* The expression to evaluate for each possible constructor *)
      * texpr option (* The expression to evaluate if no contructor match *)
  | TGetField of
      texpr * int (* Retrive one of the expression of a symbol contructor *)

type tpattern = { pat : tpat_kind; pat_typ : ttyp }
(** A typed pattern, they are not used in the TAst. *)

and tpat_kind =
  | TPatWildcard
  | TPatVar of VarId.t
  | TPatConstant of tconst
  | TPatConstructor of string * tpattern list

type symbol_decl = {
  symbid : string;  (** Id of the symbol *)
  constrs : ttyp list SMap.t;  (** Defined constructors *)
  constrs_arity : int SMap.t;  (** Number of argument of each contructor *)
  tvars : string list;  (** type variables used in the symbol type in order *)
  arity : int;  (** Arity of the symbol type *)
}

type instance = TInstance of string * ttyp list

type schema_decl = {
  tvars : SSet.t;  (** Type variable occuring in this schema *)
  req : instance list;  (** Requred instances *)
  prod : instance;  (** Instance producted *)
}

type fun_decl = {
  fun_name : string;  (** Id of the function *)
  tvars : SSet.t;  (** Type variables of the function declaration *)
  finsts : instance list;  (** The instances on which the functions depend *)
  args : ttyp list;  (** Expected type of the arguments *)
  arity : int;  (** Number of argument of the function *)
  typ : ttyp;  (** Return type of the function *)
}

type class_decl = {
  class_name : string;  (** Name of the class *)
  carity : int;  (** Number of type argument of the class *)
  tvars : string list;  (** type variables used in the class, in order *)
  cfun_decls : fun_decl SMap.t;  (** Functions defined in the class *)
}

type local_env = {
  tvars : SSet.t;
      (** Set of all type variable defined in the local environment *)
  vartype : (ttyp * VarId.t) SMap.t;
      (** Maps the variable name to their type and unique id *)
  instances : instance list;  (** Instances available in the local environment *)
}

type global_env = {
  symbsdecls : symbol_decl SMap.t;
      (** Maps each symbol type name to their declaration *)
  constrsdecls : symbol_decl SMap.t;
      (** Maps each constructor name to its symbol type declaration *)
  fundecls : fun_decl SMap.t;  (** Maps each function to its declaration *)
  classdecls : class_decl SMap.t;
      (** Maps each class name to its declaration *)
  schemadecls : schema_decl list SMap.t;
      (** Maps each class with the list of declared schemas which can
          produce an instance of this class. *)
}

type fun_impl = {
  fun_name : string; (* The declaration of this implementation *)
  fvars : VarId.t list; (* argument of the function, in order *)
  farity : int; (* number of argument *)
  fun_expr : texpr; (* body of the function *)
  associed_instance : instance option;
      (* the instance in witch the function as been declared *)
}
(** Describe the implemntation of a function *)

type tprogram = fun_impl list SMap.t
(* Maps each function name to the list of all implentations. *)

(** [_cbs] create a built-in symbol of arity 0 *)
let _cbs name =
  ( name,
    {
      symbid = name;
      constrs = SMap.empty;
      constrs_arity = SMap.empty;
      tvars = [];
      arity = 0;
    } )

let _unit_name = "Unit"
let _bool_name = "Boolean"
let _int_name = "Int"
let _str_name = "String"
let _effect_name = "Effect"
let _show_class_name = "Show"

(* The builtins types *)
let unit_t = TSymbol (_unit_name, [])
let bool_t = TSymbol (_bool_name, [])
let int_t = TSymbol (_int_name, [])
let string_t = TSymbol (_str_name, [])
let effect_t t = TSymbol (_effect_name, [ t ])

(* The builtins functions *)
let not_fid = "not"
let mod_fid = "mod"
let log_fid = "log"
let pure_fid = "pure"
let show_fid = "show"
let _q_var_a = TQuantifiedVar "a"

(** A default global environment with:
    - builtins types: Unit, Boolean, Int, String, and Effect a
    - no contructors
    - builtins function: not, mod, log, pure
    - builtin class: Show a
    - builtins instances: Show Int, Show String
    - no schemas. *)
let default_genv =
  {
    symbsdecls =
      SMap.of_list
        [
          _cbs _unit_name;
          _cbs _bool_name;
          _cbs _int_name;
          _cbs _str_name;
          ( _effect_name,
            {
              symbid = "Effect";
              constrs = SMap.empty;
              constrs_arity = SMap.empty;
              tvars = [ "a" ];
              arity = 1;
            } );
        ];
    constrsdecls = SMap.empty;
    fundecls =
      SMap.of_list
        [
          ( not_fid,
            {
              fun_name = not_fid;
              tvars = SSet.empty;
              finsts = [];
              args = [ bool_t ];
              arity = 1;
              typ = bool_t;
            } );
          ( mod_fid,
            {
              fun_name = mod_fid;
              tvars = SSet.empty;
              finsts = [];
              args = [ int_t; int_t ];
              arity = 2;
              typ = int_t;
            } );
          ( log_fid,
            {
              fun_name = log_fid;
              tvars = SSet.empty;
              finsts = [];
              args = [ string_t ];
              arity = 1;
              typ = effect_t unit_t;
            } );
          ( pure_fid,
            {
              fun_name = pure_fid;
              tvars = SSet.singleton "a";
              finsts = [];
              args = [ _q_var_a ];
              arity = 1;
              typ = effect_t _q_var_a;
            } );
          ( show_fid,
            {
              fun_name = show_fid;
              tvars = SSet.singleton "a";
              finsts = [ TInstance (_show_class_name, [ _q_var_a ]) ];
              args = [ _q_var_a ];
              arity = 1;
              typ = string_t;
            } );
        ];
    classdecls =
      SMap.singleton _show_class_name
        {
          class_name = _show_class_name;
          carity = 1;
          tvars = [ "a" ];
          cfun_decls =
            SMap.singleton show_fid
              {
                fun_name = show_fid;
                tvars = SSet.empty;
                finsts = [];
                args = [ _q_var_a ];
                arity = 1;
                typ = string_t;
              };
        };
    schemadecls =
      SMap.singleton _show_class_name
        [
          {
            req = [];
            prod = TInstance (_show_class_name, [ int_t ]);
            tvars = SSet.empty;
          };
          {
            req = [];
            prod = TInstance (_show_class_name, [ bool_t ]);
            tvars = SSet.empty;
          };
        ];
  }

(* Functions to tests expression types *)
let is_unit_t t =
  match unfold t with
  | TSymbol (sid, []) when sid = _unit_name -> true
  | _ -> false

let is_bool_t t =
  match unfold t with
  | TSymbol (sid, []) when sid = _bool_name -> true
  | _ -> false

let is_int_t t =
  match unfold t with
  | TSymbol (sid, []) when sid = _int_name -> true
  | _ -> false

let is_string_t t =
  match unfold t with
  | TSymbol (sid, []) when sid = _str_name -> true
  | _ -> false

(** [pat_constr_set genv typ] returns the list of known "pattern contructors"
    possible for this type. *)
let pat_constr_set genv typ =
  match unfold typ with
  | TQuantifiedVar _ | TVar _ ->
      (* We dont know the type we match on. So no constructor possible *)
      CompPatConstrSet.empty
  | TSymbol (s, _) as t ->
      if is_bool_t t then
        (* its a boolean, so the possible constructors are "true" or "false" *)
        CompPatConstrSet.of_list
          [
            TConstantConstr (TBoolConstant true);
            TConstantConstr (TBoolConstant false);
          ]
      else
        (* It's either a builtin type without known construtors
           (Int, String, Unit, Effect) or an introduced one with its list of
           symbol constructors *)
        let decl = SMap.find s genv.symbsdecls in
        SMap.fold
          (fun x _ acc -> CompPatConstrSet.add (TSymbolConstr x) acc)
          decl.constrs_arity CompPatConstrSet.empty
