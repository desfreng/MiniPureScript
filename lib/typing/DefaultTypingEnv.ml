open TypedAst

(** [_cbs] create a built-in symbol of arity 0 *)
let cbs name =
  ( name
  , {symbol_constr= Constructor.Map.empty; symbol_tvars= []; symbol_arity= 0} )

let unit_sid, bool_sid, int_sid, str_sid, effect_sid =
  ( Symbol.fresh "Unit"
  , Symbol.fresh "Boolean"
  , Symbol.fresh "Int"
  , Symbol.fresh "String"
  , Symbol.fresh "Effect" )

(* The builtin types *)
let unit_t = TSymbol (unit_sid, [])

let bool_t = TSymbol (bool_sid, [])

let int_t = TSymbol (int_sid, [])

let string_t = TSymbol (str_sid, [])

let effect_t t = TSymbol (effect_sid, [t])

let not_fun_name, mod_fun_name, log_fun_name, pure_fun_name, show_fun_name =
  ("not", "mod", "log", "pure", "show")

let show_class_name = "Show"

let show_tid = TypeClass.fresh show_class_name

let bool_show_sid, int_show_sid = (Schema.fresh show_tid, Schema.fresh show_tid)

(* The builtin functions *)
let not_fid, mod_fid, log_fid, pure_fid, show_fid =
  ( Function.fresh not_fun_name None
  , Function.fresh mod_fun_name None
  , Function.fresh log_fun_name None
  , Function.fresh pure_fun_name None
  , Function.fresh show_fun_name (Some show_tid) )

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
        [ cbs unit_sid
        ; cbs bool_sid
        ; cbs int_sid
        ; cbs str_sid
        ; ( effect_sid
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
        ; (show_fid, Either.Right show_tid) ]
  ; tclass=
      (let v = QTypeVar.fresh () in
       TypeClass.Map.singleton show_tid
         { tclass_arity= 1
         ; tclass_tvars= [v]
         ; tclass_decls=
             Function.Map.singleton show_fid
               { tc_fun_args= [TQuantifiedVar v]
               ; tc_fun_arity= 1
               ; tc_fun_ret= string_t } } )
  ; schemas=
      TypeClass.Map.singleton show_tid
        [ { schema_id= int_show_sid
          ; schema_req= []
          ; schema_prod= (show_tid, [int_t])
          ; schema_tvars= QTypeVar.Set.empty }
        ; { schema_id= bool_show_sid
          ; schema_req= []
          ; schema_prod= (show_tid, [bool_t])
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
  | TSymbol (sid, []) when sid = unit_sid ->
      true
  | _ ->
      false

let is_bool_t t =
  match unfold t with
  | TSymbol (sid, []) when sid = bool_sid ->
      true
  | _ ->
      false

let is_int_t t =
  match unfold t with
  | TSymbol (sid, []) when sid = int_sid ->
      true
  | _ ->
      false

let is_string_t t =
  match unfold t with
  | TSymbol (sid, []) when sid = str_sid ->
      true
  | _ ->
      false

let is_effect_t t =
  match unfold t with
  | TSymbol (sid, [_]) when sid = effect_sid ->
      true
  | _ ->
      false

let default_fun_impl =
  List.fold_left
    (fun acc (fid, ar) ->
      Function.Map.add fid
        {tfun_id= fid; tfun_arity= ar; tfun_vars= []; tfun_texpr= None}
        acc )
    Function.Map.empty
    [(not_fid, 1); (mod_fid, 1); (log_fid, 1); (pure_fid, 1)]

let default_schema_impl =
  let default_schema_impl =
    Schema.Map.singleton bool_show_sid
      { tschema_id= bool_show_sid
      ; tschema_funs=
          Function.Map.singleton show_fid
            {tfun_id= show_fid; tfun_arity= 1; tfun_vars= []; tfun_texpr= None}
      }
  in
  Schema.Map.add int_show_sid
    { tschema_id= int_show_sid
    ; tschema_funs=
        Function.Map.singleton show_fid
          {tfun_id= show_fid; tfun_arity= 1; tfun_vars= []; tfun_texpr= None} }
    default_schema_impl
