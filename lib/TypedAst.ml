include Ids

(** Type of an expression. *)
type ttyp =
  | TQuantifiedVar of QTypeVar.t
  | TVar of {id: TypeVar.t; mutable def: ttyp option}
  | TSymbol of Symbol.t * ttyp list

(** [new_tvar ()] creates a fresh type variable, without any information about
    its value, nor its name. *)
let new_tvar () = TVar {id= TypeVar.fresh (); def= None}

(** [unfold v] unfolds recursively the "top-level" unifications of a type variable
    Invariant: if the return is a TVar, def is None.*)
let rec unfold v = match v with TVar {def= Some t; _} -> unfold t | _ -> v

(** [subst s t] applies the substitution [s] (that maps quantified variable to
    type variables) to all variables in [t] *)
let rec subst s t =
  let t = unfold t in
  match t with
  | TVar _ ->
      t
  | TSymbol (sid, args) ->
      TSymbol (sid, List.map (subst s) args)
  | TQuantifiedVar n -> (
    match Hashtbl.find_opt s n with Some t -> t | None -> t )

(** [occurs vid t] checks if the variable id [vid] occurs in the type [t] *)
let rec occurs vid t =
  match unfold t with
  | TSymbol (_, args) ->
      List.exists (occurs vid) args
  | TVar {id; _} ->
      vid = id
  | TQuantifiedVar _ ->
      false

(** [lfresh_subst l] creates a substitution of quantified variables from the
    list [l] to fresh type variables. *)
let lfresh_subst l =
  let s = Hashtbl.create 17 in
  List.iter (fun v -> Hashtbl.add s v (new_tvar ())) l ;
  s

(** [sfresh_subst s] creates a substitution of quantified variables from the
    set [s] to fresh type variables. *)
let sfresh_subst set =
  let s = Hashtbl.create 17 in
  QTypeVar.Set.iter (fun v -> Hashtbl.add s v (new_tvar ())) set ;
  s

(** The structure carried by the exception *)
type unif_error =
  | SymbolMismatch of {symb1: Symbol.t; symb2: Symbol.t}
  | VariableOccuring of {var: ttyp; typ: ttyp}
  | NotSameTypes of {t1: ttyp; t2: ttyp}

(** Exception thrown by [unify] *)
exception UnificationError of unif_error

(** [unify t1 t2] attempts to find a substitution for the variables in [t1] and
    [t2] so that the two types are equal. If this process fails, a
    [UnificationError] is generated containing all the information indicating
    what has happened. *)
let rec unify t1 t2 =
  let t1, t2 = (unfold t1, unfold t2) in
  match (t1, t2) with
  | TSymbol (sid1, args1), TSymbol (sid2, args2) ->
      if sid1 = sid2 then List.iter2 unify args1 args2
      else raise (UnificationError (SymbolMismatch {symb1= sid1; symb2= sid2}))
  | TQuantifiedVar s1, TQuantifiedVar s2 ->
      if s1 = s2 then () else raise (UnificationError (NotSameTypes {t1; t2}))
  | TVar v, t ->
      if occurs v.id t then
        raise (UnificationError (VariableOccuring {var= TVar v; typ= t}))
      else v.def <- Some t
  | _, TVar _ ->
      unify t2 t1
  | TSymbol _, TQuantifiedVar _ | TQuantifiedVar _, TSymbol _ ->
      raise (UnificationError (NotSameTypes {t1; t2}))

(** [can_unify t1 t2] check if [t1] can be unified with [t2].
    Beware ! We modify the variables ! *)
let can_unify t1 t2 = try unify t1 t2 ; true with UnificationError _ -> false

(** [copy t] creates a copy of the type [t] *)
let rec copy t =
  match unfold t with
  | TVar _ ->
      new_tvar ()
  | TQuantifiedVar s ->
      TQuantifiedVar s
  | TSymbol (s, args) ->
      TSymbol (s, List.map copy args)

(** A constant in the Typed AST *)
module type Constant = sig
  type t = TUnit | TBool of bool | TInt of int | TString of string

  module Map : Map.S with type key = t

  module Set : Set.S with type elt = t

  type 'a map = 'a Map.t

  type set = Set.t
end

module Constant : Constant = struct
  type t = TUnit | TBool of bool | TInt of int | TString of string

  type const = t

  module M = struct
    type t = const

    let compare (x : t) (y : t) : int = Stdlib.compare x y
  end

  module Map = Map.Make (M)
  module Set = Set.Make (M)

  type 'a map = 'a Map.t

  type set = Set.t
end

type res_inst_kind =
  | (* This refers to the [i]th instance given as argument of the function. *)
    ArgumentInstance of int
  | (* This refers an instance defined in the global environment. *)
    GlobalInstance of Schema.t
  | (* This refers a schema instancied with the following instance arguments. *)
    GlobalSchema of (Schema.t * res_inst_kind list)

type resolved_inst = res_inst_kind Lazy.t

(** Expression type, with every type possible. *)
type texpr = {expr: texpr_kind; expr_typ: ttyp}

and texpr_kind =
  | TConstant of Constant.t
  | TVariable of Variable.t
  | TNeg of texpr
  | TBinOp of texpr * Ast.binop * texpr
  | (* "Regular" Function application *)
    TRegularFunApp of
      Function.t (* the function id *)
      * resolved_inst list (* the list of instances needed *)
      * texpr list (* the list of argument *)
  | (* Type-Class Function application *)
    TTypeClassFunApp of
      resolved_inst (* the instance in which the function called is defined *)
      * Function.t (* the function id *)
      * texpr list (* the list of argument *)
  | TConstructor of Constructor.t * texpr list (* Constructor application *)
  | TIf of texpr * texpr * texpr
  | TBlock of texpr list
  | TLet of Variable.t * texpr * texpr
  | TConstantCase of
      texpr (* The expression we need to compare to each constant *)
      * texpr Constant.map
      (* The expression to evaluate for each possible constant (of the same type) *)
      * texpr option (* The expression to evaluate if no constants match *)
  | TContructorCase of
      texpr (* The expression for which we are looking at the constructor *)
      * texpr Constructor.map
      (* The expression to evaluate for each possible constructor *)
      * texpr option (* The expression to evaluate if no constructor match *)
  | TGetField of
      texpr * int (* Retrieve one of the expression of a symbol constructor *)

(** A typed pattern, they are not used in the TAst. *)
type tpattern = {pat: tpat_kind; pat_typ: ttyp}

and tpat_kind =
  | TPatWildcard
  | TPatVar of Variable.t
  | TPatConstant of Constant.t
  | TPatConstructor of Constructor.t * tpattern list

type symbol =
  { symbol_constr: (ttyp list * int) Constructor.map  (** Defined constructors *)
  ; symbol_tvars: QTypeVar.t list
        (** type variables used in the symbol type in order *)
  ; symbol_arity: int  (** Arity of the symbol type *) }

type schema =
  { schema_id: Schema.t  (** Unique id of this schema. *)
  ; schema_tvars: QTypeVar.set  (** Type variable occurring in this schema *)
  ; schema_req: (TypeClass.t * ttyp list) list  (** Required instances *)
  ; schema_prod: TypeClass.t * ttyp list  (** Instance produced *) }

type funct =
  { fun_tvars: QTypeVar.set  (** Type variables of the function declaration *)
  ; fun_insts: (TypeClass.t * ttyp list) list
        (** The instances on which the functions depend *)
  ; fun_args: ttyp list  (** Expected type of the arguments *)
  ; fun_arity: int  (** Number of argument of the function *)
  ; fun_ret: ttyp  (** Return type of the function *) }

module SMap = Map.Make (String)
module SSet = Set.Make (String)

type tclass =
  { tclass_arity: int  (** Number of type argument of the class *)
  ; tclass_tvars: QTypeVar.t list
        (** type variables used in the class, in order *)
  ; tclass_decls: (ttyp list * int * ttyp) SMap.t
        (** Functions defined in the class *) }

type local_env =
  { tvars: QTypeVar.t SMap.t
        (** Maps all type variable defined in the local environment to their id. *)
  ; vartype: (ttyp * Variable.t) SMap.t
        (** Maps the variable name to their type and unique id *)
  ; instances: (int * TypeClass.t * ttyp list) list TypeClass.map
        (** Instances available in the local environment with their argument position *)
  }

type global_env =
  { symbols: symbol Symbol.map
        (** Maps each symbol type name to their declaration *)
  ; funs: (funct, TypeClass.t) Either.t Function.map
        (** Maps each function to its declaration: as a function or in a type class. *)
  ; tclass: tclass TypeClass.map  (** Maps each class name to its declaration *)
  ; schemas: schema list TypeClass.map
        (** Maps each class with the list of declared schemas which can
          produce an instance of this class.
          Instance with no requirement are considered as a schema. *)
  }

(** Describe the implementation of a function *)
type tfun =
  { tfun_id: Function.t (* id of the function implemented *)
  ; tfun_vars: Variable.t list (* argument of the function, in order *)
  ; tfun_arity: int (* number of argument *)
  ; tfun_texpr: (texpr, string) Either.t (* body of the function *) }

type tschema =
  { tschema_id: Schema.t (* id of the shema implemented *)
  ; tschema_funs: tfun Function.map
        (* maps each function defined in this schema to its implementation. *)
  }

type tprogram =
  { tfuns: tfun Function.map
        (* maps each "normal" function definition to its implementation *)
  ; tschemas: tschema Schema.map (* maps each schema to its implementation *)
  ; genv: global_env (* The resulting typing environment. *)
  ; main_id: Function.t (* id of the program entry point *) }
