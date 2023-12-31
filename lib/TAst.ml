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
  | SymbolMismatch of {symb1: string; symb2: string}
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
      else
        raise
          (UnificationError
             (SymbolMismatch {symb1= Symbol.name sid1; symb2= Symbol.name sid2})
          )
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

(** Expression type, with every type possible. *)
type texpr = {expr: texpr_kind; expr_typ: ttyp}

and texpr_kind =
  | TConstant of Constant.t
  | TVariable of Variable.t
  | TNeg of texpr
  | TBinOp of texpr * Ast.binop * texpr
  | TApp of Function.t * texpr list (* Function application *)
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

type constructor = {constr_args: ttyp list; constr_arity: int}

type symbol =
  { symbol_constr: constructor Constructor.map  (** Defined constructors *)
  ; symbol_tvars: QTypeVar.t list
        (** type variables used in the symbol type in order *)
  ; symbol_arity: int  (** Arity of the symbol type *) }

type instance = {inst_class: TypeClass.t; inst_args: ttyp list}

type schema =
  { schema_tvars: QTypeVar.set  (** Type variable occurring in this schema *)
  ; schema_req: instance list  (** Required instances *)
  ; schema_prod: instance  (** Instance produced *) }

type funct =
  { fun_tvars: QTypeVar.set  (** Type variables of the function declaration *)
  ; fun_insts: instance list  (** The instances on which the functions depend *)
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
  ; instances: instance list
        (** Instances available in the local environment *) }

type global_env =
  { symbols: symbol Symbol.map
        (** Maps each symbol type name to their declaration *)
  ; funs: funct Function.map  (** Maps each function to its declaration *)
  ; tclass: tclass TypeClass.map  (** Maps each class name to its declaration *)
  ; schemas: schema list TypeClass.map
        (** Maps each class with the list of declared schemas which can
          produce an instance of this class.
          Instance with no requirement are considered as a schema. *)
  }

(** Describe the implementation of a function *)
type fimpl =
  { fimpl_vars: Variable.t list (* argument of the function, in order *)
  ; fimpl_arity: int (* number of argument *)
  ; fimpl_expr: texpr (* body of the function *)
  ; associed_instance: instance option
        (* the instance in witch the function as been declared *) }

type tprogram = fimpl list SMap.t
(* Maps each function name to the list of all implantations. *)

(** [_cbs] create a built-in symbol of arity 0 *)
let _cbs name =
  ( name
  , {symbol_constr= Constructor.Map.empty; symbol_tvars= []; symbol_arity= 0} )

let _unit_n, _bool_n, _int_n, _str_n, _effect_n =
  ( Symbol.fresh "Unit"
  , Symbol.fresh "Boolean"
  , Symbol.fresh "Int"
  , Symbol.fresh "String"
  , Symbol.fresh "Effect" )

(* The builtin types *)
let unit_t = TSymbol (_unit_n, [])

let bool_t = TSymbol (_bool_n, [])

let int_t = TSymbol (_int_n, [])

let string_t = TSymbol (_str_n, [])

let effect_t t = TSymbol (_effect_n, [t])

let _show_fun_name = "show"

(* The builtin functions *)
let not_fid, mod_fid, log_fid, pure_fid, show_fid =
  ( Function.fresh "not"
  , Function.fresh "mod"
  , Function.fresh "log"
  , Function.fresh "pure"
  , Function.fresh _show_fun_name )

let _show_class_name = "Show"

let _show_cls_n = TypeClass.fresh _show_class_name

(** A default global environment with:
    - builtin types: Unit, Boolean, Int, String, and Effect a
    - no constructors
    - builtin function: not, mod, log, pure
    - builtin class: Show a
    - builtin instances: Show Int, Show String
    - no schemas. *)
let default_genv =
  { symbols=
      List.fold_left
        (fun m (k, v) -> Symbol.Map.add k v m)
        Symbol.Map.empty
        [ _cbs _unit_n
        ; _cbs _bool_n
        ; _cbs _int_n
        ; _cbs _str_n
        ; ( _effect_n
          , { symbol_constr= Constructor.Map.empty
            ; symbol_tvars= [QTypeVar.fresh ()]
            ; symbol_arity= 1 } ) ]
  ; funs=
      List.fold_left
        (fun m (k, v) -> Function.Map.add k v m)
        Function.Map.empty
        [ ( not_fid
          , { fun_tvars= QTypeVar.Set.empty
            ; fun_insts= []
            ; fun_args= [bool_t]
            ; fun_arity= 1
            ; fun_ret= bool_t } )
        ; ( mod_fid
          , { fun_tvars= QTypeVar.Set.empty
            ; fun_insts= []
            ; fun_args= [int_t; int_t]
            ; fun_arity= 2
            ; fun_ret= int_t } )
        ; ( log_fid
          , { fun_tvars= QTypeVar.Set.empty
            ; fun_insts= []
            ; fun_args= [string_t]
            ; fun_arity= 1
            ; fun_ret= effect_t unit_t } )
        ; ( pure_fid
          , let v = QTypeVar.fresh () in
            { fun_tvars= QTypeVar.Set.singleton v
            ; fun_insts= []
            ; fun_args= [TQuantifiedVar v]
            ; fun_arity= 1
            ; fun_ret= effect_t (TQuantifiedVar v) } )
        ; ( show_fid
          , let v = QTypeVar.fresh () in
            { fun_tvars= QTypeVar.Set.singleton v
            ; fun_insts=
                [{inst_class= _show_cls_n; inst_args= [TQuantifiedVar v]}]
            ; fun_args= [TQuantifiedVar v]
            ; fun_arity= 1
            ; fun_ret= string_t } ) ]
  ; tclass=
      (let v = QTypeVar.fresh () in
       TypeClass.Map.singleton _show_cls_n
         { tclass_arity= 1
         ; tclass_tvars= [v]
         ; tclass_decls=
             SMap.singleton _show_fun_name ([TQuantifiedVar v], 1, string_t) }
      )
  ; schemas=
      TypeClass.Map.singleton _show_cls_n
        [ { schema_req= []
          ; schema_prod= {inst_class= _show_cls_n; inst_args= [int_t]}
          ; schema_tvars= QTypeVar.Set.empty }
        ; { schema_req= []
          ; schema_prod= {inst_class= _show_cls_n; inst_args= [bool_t]}
          ; schema_tvars= QTypeVar.Set.empty } ] }

(** A default local environment with a constant unit. *)
let default_lenv =
  { tvars= SMap.empty
  ; instances= []
  ; vartype=
      (let v = Variable.fresh "unit" in
       SMap.singleton "unit" (unit_t, v) ) }

(* Functions to tests expression types *)
let is_unit_t t =
  match unfold t with
  | TSymbol (sid, []) when sid = _unit_n ->
      true
  | _ ->
      false

let is_bool_t t =
  match unfold t with
  | TSymbol (sid, []) when sid = _bool_n ->
      true
  | _ ->
      false

let is_int_t t =
  match unfold t with TSymbol (sid, []) when sid = _int_n -> true | _ -> false

let is_string_t t =
  match unfold t with TSymbol (sid, []) when sid = _str_n -> true | _ -> false

let is_effect_t t =
  match unfold t with
  | TSymbol (sid, [_]) when sid = _effect_n ->
      true
  | _ ->
      false
