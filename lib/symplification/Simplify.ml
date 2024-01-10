open CommonSymplify
open OperationSymplify
open ConstantMachingSymplify

let introduce_let typ l =
  (* We introduce a new variable for each expression that is not a variable
     We return the function to close the future expression and the list of
     variable corresponding to each expression with their type *)
  List.fold_left_map
    (fun close arg ->
      match arg.symp_expr with
      | SVariable v ->
          (close, Either.Left v)
      | SConstant c ->
          (close, Either.Right c)
      | _ ->
          let varg = Variable.fresh "" in
          ((fun e -> mk_sexpr typ (SLet (varg, arg, close e))), Either.Left varg)
      )
    Fun.id l

let mk_binop typ lhs op rhs =
  match op with
  | Ast.Eq ->
      mk_eq typ lhs rhs
  | Neq ->
      mk_neq typ lhs rhs
  | Gt ->
      mk_gt typ lhs rhs
  | Ge ->
      mk_ge typ lhs rhs
  | Lt ->
      mk_lt typ lhs rhs
  | Le ->
      mk_le typ lhs rhs
  | Plus ->
      mk_add typ lhs rhs
  | Minus ->
      mk_sub typ lhs rhs
  | Mul ->
      mk_mul typ lhs rhs
  | Div ->
      mk_div typ lhs rhs
  | Concat ->
      mk_str_concat typ lhs rhs
  | And ->
      mk_and typ lhs rhs
  | Or ->
      mk_or typ lhs rhs

let mk_fun_call typ fid instl args =
  match fid with
  | x when x = not_fid -> (
    match (instl, args) with
    | [], [x] ->
        mk_not typ x
    | _ ->
        (* Wrongly typed not function => Impossible *)
        assert false )
  | x when x = mod_fid -> (
    match (instl, args) with
    | [], [lhs; rhs] ->
        mk_mod typ lhs rhs
    | _ ->
        (* Wrongly typed mod function => Impossible *)
        assert false )
  | _ ->
      mk_sexpr typ (SFunctionCall (fid, instl, args))

let mk_inst_call typ inst fid args =
  match fid with
  | x when x = show_fid -> (
    match args with
    | [x] -> (
      match x.symp_expr with
      | SConstant (Bool b) ->
          mk_const typ (String (string_of_bool b))
      | SConstant (Int i) ->
          mk_const typ (String (string_of_int i))
      | _ ->
          mk_sexpr typ (SInstanceCall (inst, fid, args)) )
    | _ ->
        (* Wrongly typed show function => Impossible *)
        assert false )
  | _ ->
      mk_sexpr typ (SInstanceCall (inst, fid, args))

let mk_constr typ cid args = mk_sexpr typ (SConstructor (cid, args))

let rec simplify_expr sigma e =
  let expr, typ = (e.expr, e.expr_typ) in
  match expr with
  | TConstant c ->
      mk_const typ c
  | TVariable v ->
      mk_var sigma typ v
  | TNeg e ->
      let e = simplify_expr sigma e in
      mk_neg typ e
  | TBinOp (lhs, op, rhs) ->
      let lhs = simplify_expr sigma lhs in
      let rhs = simplify_expr sigma rhs in
      mk_binop typ lhs op rhs
  | TRegularFunApp (fid, instl, args) ->
      let args = List.map (simplify_expr sigma) args in
      let instl = List.map Lazy.force instl in
      mk_fun_call typ fid instl args
  | TTypeClassFunApp (inst, fid, args) ->
      let args = List.map (simplify_expr sigma) args in
      let inst = Lazy.force inst in
      mk_inst_call typ inst fid args
  | TConstructor (cstr, args) ->
      let args = List.map (simplify_expr sigma) args in
      mk_constr typ cstr args
  | TIf (cond, tb, fb) ->
      let cond = simplify_expr sigma cond in
      let tb = simplify_expr sigma tb in
      let fb = simplify_expr sigma fb in
      mk_if typ cond tb fb
  | TBlock l ->
      let l = List.map (simplify_expr sigma) l in
      mk_sexpr typ (SBlock l)
  | TLet (v, x, y) -> (
      (* let v = x in y *)
      let x = simplify_expr sigma x in
      match x.symp_expr with
      | SConstant c ->
          (* We have a let v = constant in y
             So we add the substitution v -> constant *)
          Hashtbl.add sigma v (Right c) ;
          simplify_expr sigma y
      | SVariable v' ->
          (* We have a let v = variable v' in y
             So we add the substitution v -> sigma (v') *)
          Hashtbl.add sigma v (subst sigma v') ;
          simplify_expr sigma y
      | _ ->
          (* No easy simplification possible *)
          Hashtbl.add sigma v (Left v) ;
          let y = simplify_expr sigma y in
          mk_sexpr typ (SLet (v, x, y)) )
  | TBind (v, v', y) ->
      (* We have a let v = v' in y
         So we add the substitution v -> sigma (v') *)
      Hashtbl.add sigma v (subst sigma v') ;
      simplify_expr sigma y
  | TStringCase (var, var_typ, branchs, other) ->
      let var = subst sigma var in
      let branchs = SMap.map (simplify_expr sigma) branchs in
      let other = simplify_expr sigma other in
      mk_string_case typ var var_typ branchs other
  | TIntCase (var, var_typ, branchs, other) ->
      let var = subst sigma var in
      let branchs = IMap.map (simplify_expr sigma) branchs in
      let other = simplify_expr sigma other in
      mk_int_case typ var var_typ branchs other
  | TContructorCase (var, symb, branchs, other) ->
      let var =
        match subst sigma var with
        | Either.Left v ->
            v
        | Either.Right _ ->
            (* A constructor pattern matching over a constant ?
               Not well typed ! *)
            assert false
      in
      let branchs = Constructor.Map.map (simplify_expr sigma) branchs in
      let other = Option.map (simplify_expr sigma) other in
      mk_sexpr typ (SContructorCase (var, symb, branchs, other))
  | TGetField (var, f) ->
      let var =
        match subst sigma var with
        | Either.Left v ->
            v
        | Either.Right _ ->
            (* Getting a field of a constant ?
               Not well typed ! *)
            assert false
      in
      mk_sexpr typ (SGetField (var, f))

let simplfy_fun tfun =
  let sigma =
    let sigma = Hashtbl.create 17 in
    List.iter (fun v -> Hashtbl.add sigma v (Either.Left v)) tfun.tfun_vars ;
    sigma
  in
  let body = simplify_expr sigma tfun.tfun_texpr in
  { sfun_id= tfun.tfun_id
  ; sfun_arity= tfun.tfun_arity
  ; sfun_body= body
  ; sfun_vars= tfun.tfun_vars
  ; sfun_insts= tfun.tfun_insts }

let simplify_schema tshema =
  let sschema_funs = Function.Map.map simplfy_fun tshema.tschema_funs in
  { sschema_id= tshema.tschema_id
  ; sschema_funs
  ; sschema_insts= tshema.tschema_insts
  ; sschema_nb_funs= tshema.tschema_nb_funs }

let simplify_program p =
  let sfuns = Function.Map.map simplfy_fun p.tfuns in
  let sschemas = Schema.Map.map simplify_schema p.tschemas in
  {sfuns; sschemas; sprog_main= p.main_id; sprog_genv= p.genv}
