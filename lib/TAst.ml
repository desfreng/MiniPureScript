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
        match name with
        | Some n -> n
        | None -> Format.asprintf "%s%i" E.type_name !cpt )

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
  | TSymbol (did, args) -> TSymbol (did, List.map (subst s) args)
  | TQuantifiedVar n -> (
      match SMap.find_opt n s with Some t -> t | None -> t)

(** [occurs vid t] checks if the variable id [vid] occurs in the type [t]*)
let rec occurs vid t =
  match unfold t with
  | TSymbol (_, args) -> List.exists (occurs vid) args
  | TVar { id; _ } -> vid = id
  | TQuantifiedVar _ -> false

(** [lfresh_subst l] creates a substitution of quantified variables from the
    list [l] for fresh type variables. *)
let lfresh_subst =
  List.fold_left (fun acc v -> SMap.add v (new_tvar ()) acc) SMap.empty

(** [sfresh_subst s] creates a substitution of quantified variables from the
    set [s] for fresh type variables. *)
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
  | TSymbol (did1, args1), TSymbol (did2, args2) ->
      if did1 = did2 then List.iter2 unify args1 args2
      else
        raise (UnificationError (SymbolMismatch { symb1 = did1; symb2 = did2 }))
  | TQuantifiedVar s1, TQuantifiedVar s2 ->
      if s1 = s2 then () else raise (UnificationError (NotSameTypes { t1; t2 }))
  | TVar v, t | t, TVar v ->
      if occurs v.id t then
        raise (UnificationError (VariableOccuring { var = TVar v; typ = t }))
      else v.def <- Some t
  | TSymbol _, TQuantifiedVar _ | TQuantifiedVar _, TSymbol _ ->
      raise (UnificationError (NotSameTypes { t1; t2 }))

(** Id of a variable. *)
module VarId = IntId (struct
  let type_name = "var"
end)

(** Id of a Constructor *)
module ConstId = IntId (struct
  let type_name = "const"
end)

module ConstMap = Map.Make (ConstId)

(** A constant in the Typped AST *)
type tconst =
  | TConstUnit
  | TConstBool of bool
  | TConstInt of int
  | TConstString of string

type texpr = { expr : texpr_kind; expr_typ : ttyp }
(** Expression type *)

and texpr_kind =
  | TConstant of tconst
  | TVariable of VarId.t
  | TBinOp of texpr * Ast.binop * texpr
  | TApp of string * texpr list (* Function application *)
  | TConstructor of ConstId.t * texpr list (* Constructor application *)
  | TIf of texpr * texpr * texpr
  | TBlock of texpr list
  | TLet of VarId.t * texpr * texpr_kind
  | TContructorCase of
      texpr (* The expression for which we are looking at the constructor *)
      * texpr ConstMap.t
      (* The expression to evaluate for each possible constructor *)
      * texpr option (* The expression to evaluate if no contructor match *)
  | TGetField of texpr * int (* Retrive the expression in a contructor *)

type tpattern = { pat : tpat_kind; pat_typ : ttyp }

and tpat_kind =
  | TPatWildcard
  | TPatVar of VarId.t
  | TPatConstant of tconst
  | TPatConstructor of ConstId.t * tpattern list

type symbol_decl = {
  symbid : string;  (** Id of the symbol *)
  consts : ttyp list ConstMap.t;  (** Defined constructors *)
  consts_arity : int ConstMap.t;  (** Number of argument of each contructor *)
  tvars : string list;  (** type variables used in the symbol type in order *)
  arity : int;  (** Arity of the symbol type *)
}

type class_decl = {
  classid : string;  (** Id of the class (name) *)
  arity : int;  (** The number of type it must be applied to. *)
}

type instance = string * ttyp list

type instance_decl = {
  inst : instance;  (** The instance declared *)
  tvars : SSet.t;  (** Type variables free *)
}

type schema_decl = {
  tvars : SSet.t;  (** Type variable occuring in this schema *)
  req : instance list;  (** Requred instances *)
  prod : instance;  (** Instance producted *)
}

type fun_decl = {
  funid : string;  (** Id of the function *)
  tvars : SSet.t;  (** Type variables of the function declaration *)
  finsts : instance list;  (** The instances on which the functions depend *)
  args : ttyp list;  (** Expected type of the arguments *)
  arity : int;  (** Number of argument of the function *)
  typ : ttyp;  (** Return type of the function *)
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
  constsdecls : (ConstId.t * symbol_decl) SMap.t;
      (** Maps each constructor name to its id and symbol type declaration *)
  fundecls : fun_decl SMap.t;  (** Maps each function to its declaration *)
  classdecl : class_decl SMap.t;  (** Maps each class name to its declaration *)
  instdecls : instance_decl list SMap.t;
      (** Maps each class with the list of instances declared for it. *)
  schemadecl : schema_decl list SMap.t;
      (** Maps each class with the list of declared schemas which can
          produce an instance of this class. *)
}

(* The builtins types *)

let unit_t : ttyp = assert false
let bool_t : ttyp = assert false
let int_t : ttyp = assert false
let string_t : ttyp = assert false
let effect_t : ttyp -> ttyp = assert false

(* Functions to tests expression types *)
let is_bool_t : ttyp -> bool = assert false
let is_int_t : ttyp -> bool = assert false
let is_string_t : ttyp -> bool = assert false
