open AllocAst
open DefaultTypingEnv
open TypedAst

type var_sub =
  | Var of Variable.t
  | Const of Constant.t
  | FieldOf of var_sub * int

type local_env =
  { var_subst: (Variable.t, var_sub) Hashtbl.t
        (** Used to eliminate redondant access to memory. *)
  ; var_pos: avar Variable.map }

let subst lenv v =
  match Hashtbl.find_opt lenv.var_subst v with Some v -> v | None -> Var v

let rec fv_loc = function
  | Var v ->
      Variable.Set.singleton v
  | Const _ ->
      Variable.Set.empty
  | FieldOf (v, _) ->
      fv_loc v

let rec fv lenv e =
  match e.expr with
  | TConstant _ ->
      Variable.Set.empty
  | TVariable v ->
      fv_loc (subst lenv v)
  | TNeg arg | TGetField (arg, _) ->
      fv lenv arg
  | TBinOp (lhs, _, rhs) ->
      Variable.Set.union (fv lenv lhs) (fv lenv rhs)
  | TRegularFunApp (_, _, args)
  | TTypeClassFunApp (_, _, args)
  | TConstructor (_, args)
  | TBlock args ->
      List.fold_left
        (fun acc e -> Variable.Set.union acc (fv lenv e))
        Variable.Set.empty args
  | TIf (cond, tb, fb) ->
      Variable.Set.union (fv lenv cond)
        (Variable.Set.union (fv lenv tb) (fv lenv fb))
  | TLet (v, a, e) ->
      let s = Variable.Set.remove v (fv lenv e) in
      Variable.Set.union s (fv lenv a)
  | TConstantCase (m, case, o) ->
      let s = fv lenv m in
      let s =
        Constant.Map.fold
          (fun _ e acc -> Variable.Set.union acc (fv lenv e))
          case s
      in
      let s =
        match o with Some o -> Variable.Set.union s (fv lenv o) | None -> s
      in
      s
  | TContructorCase (m, case, o) ->
      let s = fv lenv m in
      let s =
        Constructor.Map.fold
          (fun _ e acc -> Variable.Set.union acc (fv lenv e))
          case s
      in
      let s =
        match o with Some o -> Variable.Set.union s (fv lenv o) | None -> s
      in
      s

let fv lenv =
  List.fold_left
    (fun acc e -> Variable.Set.union acc (fv lenv e))
    Variable.Set.empty

let mk_const e c = {aexpr= AConstant c; aexpr_typ= e.expr_typ}

let mk_var e v = {aexpr= AVariable v; aexpr_typ= e.expr_typ}

let mk_neg e ae =
  match ae.aexpr with
  | AConstant (TInt i) ->
      mk_const e (TInt (-i))
  | _ ->
      {aexpr= ANeg ae; aexpr_typ= e.expr_typ}

let mk_binop e alhs op arhs =
  match op with
  | Ast.Eq -> (
    match (alhs.aexpr, arhs.aexpr) with
    | AConstant a, AConstant b ->
        mk_const e (TBool (a = b))
    | _ ->
        {aexpr= ABinOp (alhs, op, arhs); aexpr_typ= e.expr_typ} )
  | Neq -> (
    match (alhs.aexpr, arhs.aexpr) with
    | AConstant a, AConstant b ->
        mk_const e (TBool (a <> b))
    | _ ->
        {aexpr= ABinOp (alhs, op, arhs); aexpr_typ= e.expr_typ} )
  | Gt -> (
    match (alhs.aexpr, arhs.aexpr) with
    | AConstant (TInt a), AConstant (TInt b) ->
        mk_const e (TBool (a > b))
    | _ ->
        {aexpr= ABinOp (alhs, op, arhs); aexpr_typ= e.expr_typ} )
  | Ge -> (
    match (alhs.aexpr, arhs.aexpr) with
    | AConstant (TInt a), AConstant (TInt b) ->
        mk_const e (TBool (a >= b))
    | _ ->
        {aexpr= ABinOp (alhs, op, arhs); aexpr_typ= e.expr_typ} )
  | Lt -> (
    match (alhs.aexpr, arhs.aexpr) with
    | AConstant (TInt a), AConstant (TInt b) ->
        mk_const e (TBool (a < b))
    | _ ->
        {aexpr= ABinOp (alhs, op, arhs); aexpr_typ= e.expr_typ} )
  | Le -> (
    match (alhs.aexpr, arhs.aexpr) with
    | AConstant (TInt a), AConstant (TInt b) ->
        mk_const e (TBool (a <= b))
    | _ ->
        {aexpr= ABinOp (alhs, op, arhs); aexpr_typ= e.expr_typ} )
  | Plus -> (
    match (alhs.aexpr, arhs.aexpr) with
    | AConstant (TInt a), AConstant (TInt b) ->
        mk_const e (TInt (a + b))
    | AConstant (TInt 0), _ ->
        arhs
    | _, AConstant (TInt 0) ->
        alhs
    | _ ->
        {aexpr= ABinOp (alhs, op, arhs); aexpr_typ= e.expr_typ} )
  | Minus -> (
    match (alhs.aexpr, arhs.aexpr) with
    | AConstant (TInt a), AConstant (TInt b) ->
        mk_const e (TInt (a - b))
    | AConstant (TInt 0), _ ->
        mk_neg e arhs
    | _, AConstant (TInt 0) ->
        alhs
    | _ ->
        {aexpr= ABinOp (alhs, op, arhs); aexpr_typ= e.expr_typ} )
  | Mul -> (
    match (alhs.aexpr, arhs.aexpr) with
    | AConstant (TInt a), AConstant (TInt b) ->
        mk_const e (TInt (a * b))
    | AConstant (TInt 0), _ | _, AConstant (TInt 0) ->
        (* The other branch cannot make any side effect because
           it's type is Int (!= Effect a). So we don't need to evaluate it. *)
        mk_const e (TInt 0)
    | AConstant (TInt 1), _ ->
        arhs
    | _, AConstant (TInt 1) ->
        alhs
    | _ ->
        {aexpr= ABinOp (alhs, op, arhs); aexpr_typ= e.expr_typ} )
  | Div -> (
    match (alhs.aexpr, arhs.aexpr) with
    | AConstant (TInt 0), _ | _, AConstant (TInt 0) ->
        (* The other branch cannot make any side effect because
           it's type is Int (!= Effect a). So we don't need to evaluate it.

           In PureScript: forall x. x/0 = 0 *)
        mk_const e (TInt 0)
    | AConstant (TInt a), AConstant (TInt b) ->
        mk_const e (TInt (a / b))
    | _, AConstant (TInt 1) ->
        alhs
    | _ ->
        {aexpr= ABinOp (alhs, op, arhs); aexpr_typ= e.expr_typ} )
  | Concat -> (
    match (alhs.aexpr, arhs.aexpr) with
    | AConstant (TString a), AConstant (TString b) ->
        mk_const e (TString (a ^ b))
    | AConstant (TString ""), _ ->
        arhs
    | _, AConstant (TString "") ->
        alhs
    | _, _ ->
        {aexpr= ABinOp (alhs, op, arhs); aexpr_typ= e.expr_typ} )
  | And -> (
    match (alhs.aexpr, arhs.aexpr) with
    | AConstant (TBool a), AConstant (TBool b) ->
        mk_const e (TBool (a && b))
    | AConstant (TBool false), _ | _, AConstant (TBool false) ->
        (* The other branch cannot make any side effect because it's type is
           Boolean (!= Effect a). So we don't need to evaluate it. *)
        mk_const e (TBool false)
    | AConstant (TBool true), _ ->
        arhs
    | _, AConstant (TBool true) ->
        alhs
    | _ ->
        {aexpr= ABinOp (alhs, op, arhs); aexpr_typ= e.expr_typ} )
  | Or -> (
    match (alhs.aexpr, arhs.aexpr) with
    | AConstant (TBool a), AConstant (TBool b) ->
        mk_const e (TBool (a || b))
    | AConstant (TBool true), _ | _, AConstant (TBool true) ->
        (* The other branch cannot make any side effect because it's type is
           Boolean (!= Effect a). So we don't need to evaluate it. *)
        mk_const e (TBool true)
    | AConstant (TBool false), _ ->
        arhs
    | _, AConstant (TBool false) ->
        alhs
    | _ ->
        {aexpr= ABinOp (alhs, op, arhs); aexpr_typ= e.expr_typ} )

let mk_fun_call e fid instl aargs =
  match fid with
  | x when x = not_fid -> (
    match (instl, aargs) with
    | [], [x] -> (
      match x.aexpr with
      | AConstant (TBool b) ->
          mk_const e (TBool (not b))
      | _ ->
          {aexpr= AFunctionCall (fid, [], [x]); aexpr_typ= e.expr_typ} )
    | _ ->
        (* Wrongly typed not function => Impossible *)
        assert false )
  | x when x = mod_fid -> (
    match (instl, aargs) with
    | [], [a; b] -> (
      match (a.aexpr, b.aexpr) with
      | _, AConstant (TInt 0) ->
          mk_const e (TInt 0)
      | AConstant (TInt a), AConstant (TInt b) ->
          mk_const e (TInt (a mod b))
      | _ ->
          {aexpr= AFunctionCall (fid, [], [a; b]); aexpr_typ= e.expr_typ} )
    | _ ->
        (* Wrongly typed mod function => Impossible *)
        assert false )
  | _ ->
      (* NEED to make a closure if we return an effect. *)
      if is_effect_t e.expr_typ then
        {aexpr= AFunctionClosure (fid, instl, aargs); aexpr_typ= e.expr_typ}
      else {aexpr= AFunctionCall (fid, instl, aargs); aexpr_typ= e.expr_typ}

let mk_type_class_call e inst fid aargs =
  (* NEED to make a closure if we return an effect. *)
  if is_effect_t e.expr_typ then
    {aexpr= AInstanceClosure (inst, fid, aargs); aexpr_typ= e.expr_typ}
  else {aexpr= AInstanceCall (inst, fid, aargs); aexpr_typ= e.expr_typ}

let mk_constr e cid aargs =
  {aexpr= AConstructor (cid, aargs); aexpr_typ= e.expr_typ}

let mk_if e acond atb afb =
  match acond.aexpr with
  | AConstant (TBool true) ->
      atb
  | AConstant (TBool false) ->
      afb
  | _ ->
      {aexpr= AIf (acond, atb, afb); aexpr_typ= e.expr_typ}

let mk_block_closure e label vars =
  {aexpr= ALocalClosure (label, vars); aexpr_typ= e.expr_typ}

let mk_do_effect e ae =
  (* match ae.aexpr with
     | AFunctionClosure (fid, instl, aargs) ->
         {aexpr= AFunctionCall (fid, instl, aargs); aexpr_typ= e.expr_typ}
     | AInstanceClosure (inst, fid, aargs) ->
         {aexpr= AInstanceCall (inst, fid, aargs); aexpr_typ= e.expr_typ}
     | _ -> *)
  {aexpr= ADoEffect ae; aexpr_typ= e.expr_typ}

let mk_let e v x y = {aexpr= ALet (v, x, y); aexpr_typ= e.expr_typ}

let mk_constant_case e pat branchs other =
  {aexpr= AConstantCase (pat, branchs, other); aexpr_typ= e.expr_typ}

let mk_constructor_case e pat branchs other =
  {aexpr= AContructorCase (pat, branchs, other); aexpr_typ= e.expr_typ}

let mk_get_field e ae field =
  match ae.aexpr with
  | AConstructor (_, aargs) ->
      List.nth aargs field
  | _ ->
      {aexpr= AGetField (ae, field); aexpr_typ= e.expr_typ}

let rec mk_var_pos e lenv = function
  | Var var ->
      let var_pos = Variable.Map.find var lenv.var_pos in
      mk_var e var_pos
  | Const c ->
      mk_const e c
  | FieldOf (var, f) ->
      mk_get_field e (mk_var_pos e lenv var) f

let rec allocate_expr fid lenv fp_pos e =
  match e.expr with
  | TConstant c ->
      (mk_const e c, Label.Map.empty)
  | TVariable v ->
      (* We refer to an existing value, we do not make any closure here. *)
      (mk_var_pos e lenv (subst lenv v), Label.Map.empty)
  | TNeg e ->
      (* The current expression is of type Int.
         No Effect possible -> no closure added. *)
      let ae, _ = allocate_expr fid lenv fp_pos e in
      (mk_neg e ae, Label.Map.empty)
  | TBinOp (lhs, op, rhs) ->
      (* The current expression is of type Boolean, Int or String.
         No Effect possible -> no closure added. *)
      let alhs, _ = allocate_expr fid lenv fp_pos lhs in
      let arhs, _ = allocate_expr fid lenv fp_pos rhs in
      (mk_binop e alhs op arhs, Label.Map.empty)
  | TRegularFunApp (fid, instl, args) ->
      (* All closures introduced in the argument are required to be produced !
         We return them *)
      let lbl, aargs =
        List.fold_left_map
          (fun acc arg ->
            let ae, lbl = allocate_expr fid lenv fp_pos arg in
            (Label.merge_map acc lbl, ae) )
          Label.Map.empty args
      in
      (mk_fun_call e fid instl aargs, lbl)
  | TTypeClassFunApp (inst, fid, args) ->
      (* All closures introduced in the argument are required to be produced !
         We return them *)
      let lbl, aargs =
        List.fold_left_map
          (fun acc arg ->
            let ae, lbl = allocate_expr fid lenv fp_pos arg in
            (Label.merge_map acc lbl, ae) )
          Label.Map.empty args
      in
      (mk_type_class_call e inst fid aargs, lbl)
  | TConstructor (cstrn, args) ->
      (* The current expression is of type Symbol (?, ?).
         No Effect possible -> no closure needed BUT a closure can occur in
         one of the constructor's argument, and be required => We return them *)
      let lbl, aargs =
        List.fold_left_map
          (fun acc arg ->
            let ae, lbl = allocate_expr fid lenv fp_pos arg in
            (Label.merge_map acc lbl, ae) )
          Label.Map.empty args
      in
      (mk_constr e cstrn aargs, lbl)
  | TIf (cond, tb, fb) ->
      (* All closures introduced in the branches are required to be produced !
         We return them *)
      let acond, _ = allocate_expr fid lenv fp_pos cond in
      let atb, tb_lbl = allocate_expr fid lenv fp_pos tb in
      let afb, fb_lbl = allocate_expr fid lenv fp_pos fb in
      (mk_if e acond atb afb, Label.merge_map tb_lbl fb_lbl)
  | TBlock l -> (
    match l with
    | [x] ->
        allocate_expr fid lenv fp_pos x
    | l ->
        (* We do a closure here ! So : *)
        (* We compute the free vars in the do block (while performing the
           substitution !). *)
        let fv_list = Variable.Set.elements (fv lenv l) in
        (* We create a fresh label for this do block *)
        let label = Label.of_function fid "do" in
        (* We compute the position of each free variable occuring in this
           closure *)
        let vars =
          List.map (fun v -> Variable.Map.find v lenv.var_pos) fv_list
        in
        (* And we build it. *)
        let clos = mk_block_closure e label vars in
        (* Now, we process the new label. To do so, we change the location of
           the variable with their position in the closure. *)
        let closure_lenv =
          let new_var_pos, _ =
            List.fold_left
              (fun (vp, index) v ->
                ( Variable.Map.update v
                    (function
                      | None ->
                          (* v does not have a position ?! Impossible. *)
                          assert false
                      | Some _ ->
                          Some (AClosVar index) )
                    vp
                , index + word_size ) )
              (lenv.var_pos, 0) fv_list
          in
          {lenv with var_pos= new_var_pos}
        in
        let lbl, block_expr =
          List.fold_left_map
            (fun acc arg ->
              let ae, lbl = allocate_expr fid closure_lenv initial_fp arg in
              (Label.merge_map acc lbl, mk_do_effect arg ae) )
            Label.Map.empty l
        in
        let lbl = Label.Map.add label block_expr lbl in
        (clos, lbl) )
  (* let v = x in y *)
  | TLet (v, x, y) -> (
      (* No closure here, indeed :
         - If the expression x is of type Effect a, then it is yet a closure.
         - If the expression y is of type Effect a, than it will be (later) a
           closure. *)
      (* But all closures introduced in x or in y are required to be produced !
         We return them *)
      let default_let () =
        (* Default case if no substitution occurs. *)
        let ax, x_lbl = allocate_expr fid lenv fp_pos x in
        let v_pos, fp_pos = (ALocalVar fp_pos, fp_pos - word_size) in
        let lenv = {lenv with var_pos= Variable.Map.add v v_pos lenv.var_pos} in
        let ay, y_lbl = allocate_expr fid lenv fp_pos y in
        (mk_let e v_pos ax ay, Label.merge_map x_lbl y_lbl)
      in
      match x.expr with
      | TVariable v' ->
          (* we have a let v = v' in y with v and v' variables !
             So we substitute v with σ(v') in x. *)
          let v_pos = subst lenv v' in
          Hashtbl.add lenv.var_subst v v_pos ;
          allocate_expr fid lenv fp_pos y
      | TConstant c ->
          (* we have a let v = c in y with v a variable et c a constant !
             So we substitute v with c in x. *)
          Hashtbl.add lenv.var_subst v (Const c) ;
          allocate_expr fid lenv fp_pos y
      | TGetField (expr, f) -> (
        match expr.expr with
        | TVariable x ->
            Format.eprintf "%a@." Variable.pp x ;
            (* we have a let v = GetField(x, i) in ... with v and x variables !
               So we substitute v with GetField(σ(x), i) in x. *)
            let x_pos = subst lenv x in
            Hashtbl.add lenv.var_subst v (FieldOf (x_pos, f)) ;
            allocate_expr fid lenv fp_pos y
        | _ ->
            default_let () )
      | _ ->
          default_let () )
  | TConstantCase (pat, branchs, other) ->
      (* All closures introduced in the branches are required to be produced !
         We return them. We can ignore the closures produced in the argument
         because no side effect are allowed in [pat] (because of it's type). *)
      let apat, _ = allocate_expr fid lenv fp_pos pat in
      let abranchs, lbls =
        Constant.Map.fold
          (fun cst branch (nmap, lbls) ->
            let ae, lbl = allocate_expr fid lenv fp_pos branch in
            (Constant.Map.add cst ae nmap, Label.merge_map lbls lbl) )
          branchs
          (Constant.Map.empty, Label.Map.empty)
      in
      let aother, lbl =
        match other with
        | Some o ->
            let ae, lbl = allocate_expr fid lenv fp_pos o in
            (Some ae, Label.merge_map lbls lbl)
        | None ->
            (None, lbls)
      in
      (mk_constant_case e apat abranchs aother, lbl)
  | TContructorCase (pat, branchs, other) ->
      (* All closures introduced in the branches are required to be produced !
         We return them. We can ignore the closures produced in the argument
         because no side effect are allowed in [pat] (because of it's type). *)
      let apat, _ = allocate_expr fid lenv fp_pos pat in
      let abranchs, lbls =
        Constructor.Map.fold
          (fun cst branch (nmap, lbls) ->
            Format.eprintf "@.%a@." Constructor.pp cst ;
            let ae, lbl = allocate_expr fid lenv fp_pos branch in
            (Constructor.Map.add cst ae nmap, Label.merge_map lbls lbl) )
          branchs
          (Constructor.Map.empty, Label.Map.empty)
      in
      let aother, lbl =
        match other with
        | Some o ->
            let ae, lbl = allocate_expr fid lenv fp_pos o in
            (Some ae, Label.merge_map lbls lbl)
        | None ->
            (None, lbls)
      in
      (mk_constructor_case e apat abranchs aother, lbl)
  | TGetField (e, f) ->
      (* We refer to an existing value, we do not make any closure here. *)
      let ae, _ = allocate_expr fid lenv fp_pos e in
      (mk_get_field e ae f, Label.Map.empty)

let allocate_fun genv tfun =
  (* This function is compiled as a closure if its return type is Effect a. *)
  let is_closure_fun =
    let ret_t =
      match Function.Map.find tfun.tfun_id genv.funs with
      | Either.Left funct ->
          funct.fun_ret
      | Either.Right tid ->
          let tdecl = TypeClass.Map.find tid genv.tclass in
          let _, _, ret_t =
            SMap.find (Function.name tfun.tfun_id) tdecl.tclass_decls
          in
          ret_t
    in
    is_effect_t ret_t
  in
  match tfun.tfun_texpr with
  | Either.Left fun_expr ->
      let _, var_pos =
        if is_closure_fun then
          List.fold_left
            (fun (v_index, v_map) v ->
              (v_index + word_size, Variable.Map.add v (AClosVar v_index) v_map)
              )
            (0, Variable.Map.empty) tfun.tfun_vars
        else
          List.fold_left
            (fun (v_index, v_map) v ->
              (v_index + word_size, Variable.Map.add v (ALocalVar v_index) v_map)
              )
            (call_stack_size, Variable.Map.empty)
            tfun.tfun_vars
      in
      let lenv = {var_subst= Hashtbl.create 17; var_pos} in
      let ae, lbls = allocate_expr tfun.tfun_id lenv initial_fp fun_expr in
      let fun_label = Label.of_function tfun.tfun_id "" in
      { afun_id= tfun.tfun_id
      ; afun_arity= tfun.tfun_arity
      ; afun_body= Left (ae, fun_label)
      ; afun_annex= lbls }
  | Either.Right fun_impl_id ->
      { afun_id= tfun.tfun_id
      ; afun_arity= tfun.tfun_arity
      ; afun_body= Right fun_impl_id
      ; afun_annex= Label.Map.empty }

let allocate_schema genv tshema =
  let aschema_funs = Function.Map.map (allocate_fun genv) tshema.tschema_funs in
  {aschema_id= tshema.tschema_id; aschema_funs}

let allocate_tprogram p =
  let afuns = Function.Map.map (allocate_fun p.genv) p.tfuns in
  let aschemas = Schema.Map.map (allocate_schema p.genv) p.tschemas in
  {afuns; aschemas; main_id= p.main_id; genv= p.genv}
