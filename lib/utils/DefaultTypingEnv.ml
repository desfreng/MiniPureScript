open TAst

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
          , Either.Left
              { fun_tvars= QTypeVar.Set.empty
              ; fun_insts= []
              ; fun_args= [bool_t]
              ; fun_arity= 1
              ; fun_ret= bool_t } )
        ; ( mod_fid
          , Either.Left
              { fun_tvars= QTypeVar.Set.empty
              ; fun_insts= []
              ; fun_args= [int_t; int_t]
              ; fun_arity= 2
              ; fun_ret= int_t } )
        ; ( log_fid
          , Either.Left
              { fun_tvars= QTypeVar.Set.empty
              ; fun_insts= []
              ; fun_args= [string_t]
              ; fun_arity= 1
              ; fun_ret= effect_t unit_t } )
        ; ( pure_fid
          , let v = QTypeVar.fresh () in
            Either.Left
              { fun_tvars= QTypeVar.Set.singleton v
              ; fun_insts= []
              ; fun_args= [TQuantifiedVar v]
              ; fun_arity= 1
              ; fun_ret= effect_t (TQuantifiedVar v) } )
        ; (show_fid, Either.Right _show_cls_n) ]
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
        [ { schema_id= Schema.fresh ()
          ; schema_req= []
          ; schema_prod= (_show_cls_n, [int_t])
          ; schema_tvars= QTypeVar.Set.empty }
        ; { schema_id= Schema.fresh ()
          ; schema_req= []
          ; schema_prod= (_show_cls_n, [bool_t])
          ; schema_tvars= QTypeVar.Set.empty } ] }

(** A default local environment with a constant unit. *)
let default_lenv =
  { tvars= SMap.empty
  ; instances= TypeClass.Map.empty
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
