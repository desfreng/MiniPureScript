module type Id = sig
  type t

  val fresh : unit -> t
  val compare : t -> t -> int

  module Map : Map.S with type key = t
  module Set : Set.S with type elt = t

  type 'a map = 'a Map.t
  type set = Set.t
end

(** A module to manipulate unique ids. *)
module UniqueId : Id = struct
  type t = int

  let fresh =
    let cpt = ref 0 in
    fun () ->
      incr cpt;
      !cpt

  let compare (x : t) (y : t) = Stdlib.compare x y

  module Map = Map.Make (Int)
  module Set = Set.Make (Int)

  type 'a map = 'a Map.t
  type set = Set.t
end

module TVar : Id = UniqueId
(** Id of a type variable that can be unified. *)

module TQVar : Id = UniqueId
(** Id of a universally quantified type variable. *)

(** Type of an expression. *)
type ttyp =
  | TQuantifiedVar of TQVar.t
  | TVar of { id : TVar.t; mutable def : ttyp option }
  | TSymbol of string * ttyp list

(** [new_tvar ()] creates a fresh type variable, without any information about
    its value, nor its name. *)
let new_tvar () = TVar { id = TVar.fresh (); def = None }

(** [unfold v] unfolds recursively the "top-level" unifications of a type variable
    Invariant: if the return is a TVar, def is None.*)
let rec unfold v = match v with TVar { def = Some t; _ } -> unfold t | _ -> v

(** [subst s t] applies the substitution [s] (that maps quantified variable to
    type variables) to all variables in [t] *)
let rec subst s t =
  let t = unfold t in
  match t with
  | TVar _ -> t
  | TSymbol (sid, args) -> TSymbol (sid, List.map (subst s) args)
  | TQuantifiedVar n -> (
      match Hashtbl.find_opt s n with Some t -> t | None -> t)

(** [occurs vid t] checks if the variable id [vid] occurs in the type [t]*)
let rec occurs vid t =
  match unfold t with
  | TSymbol (_, args) -> List.exists (occurs vid) args
  | TVar { id; _ } -> vid = id
  | TQuantifiedVar _ -> false

(** [lfresh_subst l] creates a substitution of quantified variables from the
    list [l] to fresh type variables. *)
let lfresh_subst l =
  let s = Hashtbl.create 17 in
  List.iter (fun v -> Hashtbl.add s v (new_tvar ())) l;
  s

(** [sfresh_subst s] creates a substitution of quantified variables from the
    set [s] to fresh type variables. *)
let sfresh_subst set =
  let s = Hashtbl.create 17 in
  TQVar.Set.iter (fun v -> Hashtbl.add s v (new_tvar ())) set;
  s

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
  | TVar _ -> new_tvar ()
  | TQuantifiedVar s -> TQuantifiedVar s
  | TSymbol (s, args) -> TSymbol (s, List.map copy args)

module VarId : Id = UniqueId
(** Id of a variable. *)

(** A constant in the Typed AST *)
type tconst =
  | TUnitConstant
  | TBoolConstant of bool
  | TIntConstant of int
  | TStringConstant of string

(** A type to represent a "pattern constructor" in the TCompiledCase expression *)
type pat_constr =
  | TSymbolConstr of string (* This is a symbol "pattern constructor" *)
  | TConstantConstr of tconst (* This is a constant "pattern constructor" *)

module PatConstr = struct
  type t = pat_constr

  let compare (x : pat_constr) (y : pat_constr) : int = Stdlib.compare x y
end

module PatConstrMap = Map.Make (PatConstr)
module PatConstrSet = Set.Make (PatConstr)

(* type utexpr = { expr : utexpr_kind; expr_typ : ttyp } *)

type texpr = { expr : texpr_kind; expr_typ : ttyp }
(** Expression type, with every type possible. *)

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
      * texpr PatConstrMap.t
      (* The expression to evaluate for each possible constructor *)
      * texpr option (* The expression to evaluate if no constructor match *)
  | TGetField of
      texpr * int (* Retrieve one of the expression of a symbol constructor *)

type tpattern = { pat : tpat_kind; pat_typ : ttyp }
(** A typed pattern, they are not used in the TAst. *)

and tpat_kind =
  | TPatWildcard
  | TPatVar of VarId.t
  | TPatConstant of tconst
  | TPatConstructor of string * tpattern list

module SMap = Map.Make (String)
module SSet = Set.Make (String)

type symbol_decl = {
  symbid : string;  (** Id of the symbol *)
  constrs : ttyp list SMap.t;  (** Defined constructors *)
  constrs_arity : int SMap.t;  (** Number of argument of each constructor *)
  tvars : TQVar.t list;  (** type variables used in the symbol type in order *)
  arity : int;  (** Arity of the symbol type *)
}

type instance = TInstance of string * ttyp list

type schema_decl = {
  tvars : TQVar.set;  (** Type variable occurring in this schema *)
  req : instance list;  (** Required instances *)
  prod : instance;  (** Instance produced *)
}

type fun_decl = {
  fun_name : string;  (** Id of the function *)
  tvars : TQVar.set;  (** Type variables of the function declaration *)
  finsts : instance list;  (** The instances on which the functions depend *)
  args : ttyp list;  (** Expected type of the arguments *)
  arity : int;  (** Number of argument of the function *)
  typ : ttyp;  (** Return type of the function *)
}

type class_decl = {
  class_name : string;  (** Name of the class *)
  carity : int;  (** Number of type argument of the class *)
  tvars : TQVar.t list;  (** type variables used in the class, in order *)
  cfun_decls : fun_decl SMap.t;  (** Functions defined in the class *)
}

type local_env = {
  tvars : TQVar.t SMap.t;
      (** Maps all type variable defined in the local environment to their id. *)
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
          produce an instance of this class.
          Instance with no requirement are considered as a schema. *)
}

type fun_impl = {
  fun_name : string; (* The declaration of this implementation *)
  fvars : VarId.t list; (* argument of the function, in order *)
  farity : int; (* number of argument *)
  fun_expr : texpr; (* body of the function *)
  associed_instance : instance option;
      (* the instance in witch the function as been declared *)
}
(** Describe the implementation of a function *)

type tprogram = fun_impl list SMap.t
(* Maps each function name to the list of all implantations. *)

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

let _unit_n, _bool_n, _int_n, _str_n, _effect_n, _show_cls_n =
  ("Unit", "Boolean", "Int", "String", "Effect", "Show")

(* The builtin types *)
let unit_t = TSymbol (_unit_n, [])
let bool_t = TSymbol (_bool_n, [])
let int_t = TSymbol (_int_n, [])
let string_t = TSymbol (_str_n, [])
let effect_t t = TSymbol (_effect_n, [ t ])

(* The builtin functions *)
let not_fid = "not"
let mod_fid = "mod"
let log_fid = "log"
let pure_fid = "pure"
let show_fid = "show"

(** A default global environment with:
    - builtin types: Unit, Boolean, Int, String, and Effect a
    - no constructors
    - builtin function: not, mod, log, pure
    - builtin class: Show a
    - builtin instances: Show Int, Show String
    - no schemas. *)
let default_genv =
  {
    symbsdecls =
      SMap.of_list
        [
          _cbs _unit_n;
          _cbs _bool_n;
          _cbs _int_n;
          _cbs _str_n;
          ( _effect_n,
            {
              symbid = _effect_n;
              constrs = SMap.empty;
              constrs_arity = SMap.empty;
              tvars = [ TQVar.fresh () ];
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
              tvars = TQVar.Set.empty;
              finsts = [];
              args = [ bool_t ];
              arity = 1;
              typ = bool_t;
            } );
          ( mod_fid,
            {
              fun_name = mod_fid;
              tvars = TQVar.Set.empty;
              finsts = [];
              args = [ int_t; int_t ];
              arity = 2;
              typ = int_t;
            } );
          ( log_fid,
            {
              fun_name = log_fid;
              tvars = TQVar.Set.empty;
              finsts = [];
              args = [ string_t ];
              arity = 1;
              typ = effect_t unit_t;
            } );
          ( pure_fid,
            let v = TQVar.fresh () in
            {
              fun_name = pure_fid;
              tvars = TQVar.Set.singleton v;
              finsts = [];
              args = [ TQuantifiedVar v ];
              arity = 1;
              typ = effect_t (TQuantifiedVar v);
            } );
          ( show_fid,
            let v = TQVar.fresh () in
            {
              fun_name = show_fid;
              tvars = TQVar.Set.singleton v;
              finsts = [ TInstance (_show_cls_n, [ TQuantifiedVar v ]) ];
              args = [ TQuantifiedVar v ];
              arity = 1;
              typ = string_t;
            } );
        ];
    classdecls =
      (let v = TQVar.fresh () in
       SMap.singleton _show_cls_n
         {
           class_name = _show_cls_n;
           carity = 1;
           tvars = [ v ];
           cfun_decls =
             SMap.singleton show_fid
               {
                 fun_name = show_fid;
                 tvars = TQVar.Set.empty;
                 finsts = [];
                 args = [ TQuantifiedVar v ];
                 arity = 1;
                 typ = string_t;
               };
         });
    schemadecls =
      SMap.singleton _show_cls_n
        [
          {
            req = [];
            prod = TInstance (_show_cls_n, [ int_t ]);
            tvars = TQVar.Set.empty;
          };
          {
            req = [];
            prod = TInstance (_show_cls_n, [ bool_t ]);
            tvars = TQVar.Set.empty;
          };
        ];
  }

(** A default local environment with a constant unit. *)
let default_lenv =
  {
    tvars = SMap.empty;
    instances = [];
    vartype =
      (let v = VarId.fresh () in
       SMap.singleton "unit" (unit_t, v));
  }

(* Functions to tests expression types *)
let is_unit_t t =
  match unfold t with
  | TSymbol (sid, []) when sid = _unit_n -> true
  | _ -> false

let is_bool_t t =
  match unfold t with
  | TSymbol (sid, []) when sid = _bool_n -> true
  | _ -> false

let is_int_t t =
  match unfold t with TSymbol (sid, []) when sid = _int_n -> true | _ -> false

let is_string_t t =
  match unfold t with TSymbol (sid, []) when sid = _str_n -> true | _ -> false

let is_effect_t t =
  match unfold t with
  | TSymbol (sid, [ _ ]) when sid = _effect_n -> true
  | _ -> false

(** [pat_constr_set genv typ] returns the list of known "pattern constructors"
    possible for this type. *)
let pat_constr_set genv typ =
  match unfold typ with
  | TQuantifiedVar _ | TVar _ ->
      (* We dont know the type we match on. So no constructor possible *)
      PatConstrSet.empty
  | TSymbol (s, _) as t ->
      if is_bool_t t then
        (* its a boolean, so the possible constructors are "true" or "false" *)
        PatConstrSet.of_list
          [
            TConstantConstr (TBoolConstant true);
            TConstantConstr (TBoolConstant false);
          ]
      else
        (* It's either a builtin type without known constructors
           (Int, String, Unit, Effect) or an introduced one with its list of
           symbol constructors *)
        let decl = SMap.find s genv.symbsdecls in
        SMap.fold
          (fun x _ acc -> PatConstrSet.add (TSymbolConstr x) acc)
          decl.constrs_arity PatConstrSet.empty
