open AllocAst
open TypedAst
open DefaultTypingEnv
open Format

let setup_pp_ttyp ?(atomic = false) lenv t =
  let tvar_map = Hashtbl.create 17 in
  let qvar_map = Hashtbl.create 17 in
  SMap.iter (fun name qvid -> Hashtbl.add qvar_map qvid name) lenv.tvars ;
  let next_weak_name =
    let cpt = ref 0 in
    fun () ->
      incr cpt ;
      "'weak" ^ string_of_int !cpt
  in
  let next_qvar_name =
    let n_set =
      ref
        (String.fold_left
           (fun acc c ->
             let str = String.make 1 c in
             if SMap.mem str lenv.tvars then acc else SSet.add str acc )
           SSet.empty "abcdefghijklmnopqrstuvwxyz" )
    in
    let cpt = ref 0 in
    fun () ->
      if SSet.is_empty !n_set then (
        incr cpt ;
        "a" ^ string_of_int !cpt )
      else
        let v = SSet.choose !n_set in
        n_set := SSet.remove v !n_set ;
        v
  in
  let rec name_vars t =
    match unfold t with
    | TVar {id; _} -> (
      match Hashtbl.find_opt tvar_map id with
      | Some _ ->
          ()
      | None ->
          Hashtbl.add tvar_map id (next_weak_name ()) )
    | TQuantifiedVar id ->
        if Hashtbl.mem qvar_map id then ()
        else Hashtbl.add qvar_map id (next_qvar_name ())
    | TSymbol (_, args) ->
        List.iter name_vars args
  in
  List.iter name_vars t ;
  fun ppf t ->
    let rec pp fst ppf t =
      match unfold t with
      | TVar {id; _} ->
          Format.pp_print_string ppf (Hashtbl.find tvar_map id)
      | TQuantifiedVar x ->
          Format.pp_print_string ppf (Hashtbl.find qvar_map x)
      | TSymbol (sid, []) ->
          Symbol.pp ppf sid
      | TSymbol (sid, args) when fst ->
          Symbol.pp ppf sid ;
          List.iter (Format.fprintf ppf " %a" (pp false)) args
      | TSymbol (sid, args) ->
          Format.fprintf ppf "(%a" Symbol.pp sid ;
          List.iter (Format.fprintf ppf " %a" (pp false)) args ;
          Format.pp_print_string ppf ")"
    in
    pp (not atomic) ppf t

let setup_pp_inst lenv t =
  let pp =
    List.fold_left (fun acc (_, inst_args) -> inst_args @ acc) [] t
    |> setup_pp_ttyp ~atomic:true lenv
  in
  fun ppf (inst_cls, inst_args) ->
    TypeClass.pp ppf inst_cls ;
    List.iter (Format.fprintf ppf " %a" pp) inst_args

let setup_pp_ttyp_inst lenv ?(atomic = false) insts tl =
  let tl =
    List.fold_left (fun acc (_, inst_args) -> inst_args @ acc) tl insts
  in
  let pp = setup_pp_ttyp ~atomic:true lenv tl in
  ( (fun ppf (inst_cls, inst_args) ->
      TypeClass.pp ppf inst_cls ;
      List.iter (Format.fprintf ppf " %a" pp) inst_args )
  , setup_pp_ttyp ~atomic lenv tl )

let pp_cst ppf = function
  | Constant.Bool b ->
      pp_print_bool ppf b
  | Constant.Int i ->
      pp_print_int ppf i
  | Constant.String s ->
      fprintf ppf "\"%s\"" s
  | Constant.Unit ->
      pp_print_string ppf "unit"

let pp_binop ppf = function
  | Ast.Eq ->
      pp_print_string ppf "=="
  | Neq ->
      pp_print_string ppf "/="
  | Gt ->
      pp_print_string ppf ">"
  | Ge ->
      pp_print_string ppf ">="
  | Lt ->
      pp_print_string ppf "<"
  | Le ->
      pp_print_string ppf "<="
  | Plus ->
      pp_print_string ppf "+"
  | Minus ->
      pp_print_string ppf "-"
  | Div ->
      pp_print_string ppf "/"
  | Mul ->
      pp_print_string ppf "*"
  | Concat ->
      pp_print_string ppf "<>"
  | And ->
      pp_print_string ppf "&&"
  | Or ->
      pp_print_string ppf "||"

let rec pp_res_inst ppf = function
  | TLocalInstance i ->
      fprintf ppf "(Instance Argument %a)" Instance.pp i
  | TGlobalInstance s ->
      fprintf ppf "(Instance %a)" Schema.pp s
  | TGlobalSchema (s, args, _) ->
      fprintf ppf "@[<hv 2>(Schema %a" Schema.pp s ;
      List.iter (fprintf ppf "@,%a" pp_res_inst) args ;
      fprintf ppf ")@]"

let rec pp_texpr ppf e =
  match e.expr with
  | TConstant c ->
      fprintf ppf "@[<hv 2>(Constant %a)@]" pp_cst c
  | TVariable v ->
      fprintf ppf "@[<hv 2>(Variable %a)@]" Variable.pp v
  | TNeg x ->
      fprintf ppf "@[<hv 2>(neg@,%a)@]" pp_texpr x
  | TBinOp (lhs, op, rhs) ->
      fprintf ppf "@[<hv 2>(%a@,%a@,%a)@]" pp_binop op pp_texpr lhs pp_texpr rhs
  | TRegularFunApp (f, insts, args) ->
      fprintf ppf "@[<hv 2>(%a" Function.pp f ;
      List.iter (fun i -> fprintf ppf "@,%a" pp_res_inst (Lazy.force i)) insts ;
      List.iter (fprintf ppf "@,%a" pp_texpr) args ;
      fprintf ppf ") @]"
  | TTypeClassFunApp (i, f, args) ->
      fprintf ppf "@[<hv 2>(%a.%a" pp_res_inst (Lazy.force i) Function.pp f ;
      List.iter (fprintf ppf "@,%a" pp_texpr) args ;
      fprintf ppf ")@]"
  | TConstructor (cstr, args) -> (
    match args with
    | [] ->
        Constructor.pp ppf cstr
    | args ->
        fprintf ppf "@[<hv 2>(%a" Constructor.pp cstr ;
        List.iter (fprintf ppf "@,%a" pp_texpr) args ;
        fprintf ppf ")@]" )
  | TIf (cd, tb, fb) ->
      fprintf ppf "@[<hv 2>(if@ %a@,then@ %a@,else@ %a)@]" pp_texpr cd pp_texpr
        tb pp_texpr fb
  | TBlock l ->
      fprintf ppf "@[<hv 2>(do" ;
      List.iter (fprintf ppf "@,%a" pp_texpr) l ;
      fprintf ppf ")@]"
  | TLet (v, b, e) ->
      fprintf ppf "@[<hv 2>(let@,@[<hv 2>(%a = %a)@]@,in %a)@]" Variable.pp v
        pp_texpr b pp_texpr e
  | TBind (v, v', e) ->
      fprintf ppf "@[<hv 2>(let@,@[<hv 2>(%a = %a)@]@,in %a)@]" Variable.pp v
        Variable.pp v' pp_texpr e
  | TStringCase (v, _, c, o) ->
      fprintf ppf "@[<hv 2>(match %a@," Variable.pp v ;
      SMap.iter
        (fun c expr -> fprintf ppf "@[<hv 2>(%s =>@,%a)@]@," c pp_texpr expr)
        c ;
      fprintf ppf "@[<hv 2>_ =>@,%a@]" pp_texpr o ;
      fprintf ppf ")@]"
  | TIntCase (v, _, c, o) ->
      fprintf ppf "@[<hv 2>(match %a@," Variable.pp v ;
      IMap.iter
        (fun c expr -> fprintf ppf "@[<hv 2>(%d =>@,%a)@]@," c pp_texpr expr)
        c ;
      fprintf ppf "@[<hv 2>_ =>@,%a@]" pp_texpr o ;
      fprintf ppf ")@]"
  | TConstructorCase (v, _, c, o) ->
      fprintf ppf "@[<hv 2>(match %a@," Variable.pp v ;
      Constructor.Map.iter
        (fun c expr ->
          fprintf ppf "@[<hv 2>(%a =>@,%a)@]@," Constructor.pp c pp_texpr expr
          )
        c ;
      ( match o with
      | Some o ->
          fprintf ppf "@[<hv 2>_ =>@,%a@]" pp_texpr o
      | None ->
          () ) ;
      fprintf ppf ")@]"
  | TGetField (e, i) ->
      Format.fprintf ppf "@[<hv 2>(field %i of@ %a)@]" i Variable.pp e

let pp_schema ppf sdecl =
  match sdecl.schema_req with
  | [] ->
      let pp_inst = setup_pp_inst default_lenv [sdecl.schema_prod] in
      pp_inst ppf sdecl.schema_prod
  | [req] ->
      let pp_inst = setup_pp_inst default_lenv [sdecl.schema_prod; req] in
      fprintf ppf "%a => %a" pp_inst req pp_inst sdecl.schema_prod
  | reqs ->
      let pp_inst = setup_pp_inst default_lenv (sdecl.schema_prod :: reqs) in
      fprintf ppf "(%a) => %a"
        (pp_print_list ~pp_sep:(fun ppf _ -> pp_print_string ppf ", ") pp_inst)
        reqs pp_inst sdecl.schema_prod

let pp_fun_typ ppf (fun_inst, fun_args, fun_ret) =
  if fun_inst = [] then
    let targs = fun_args @ [fun_ret] in
    let pp_ttyp = setup_pp_ttyp default_lenv targs in
    pp_print_list
      ~pp_sep:(fun ppf () -> pp_print_string ppf " -> ")
      pp_ttyp ppf targs
  else
    let pp_inst, pp_ttyp =
      setup_pp_ttyp_inst default_lenv fun_inst (fun_ret :: fun_args)
    in
    pp_print_list
      ~pp_sep:(fun ppf () -> pp_print_string ppf " => ")
      pp_inst ppf fun_inst ;
    pp_print_string ppf " => " ;
    let targs = fun_args @ [fun_ret] in
    pp_print_list
      ~pp_sep:(fun ppf () -> pp_print_string ppf " -> ")
      pp_ttyp ppf targs

let pp_tfun genv ppf (fid, exp) =
  let fdecl =
    match Function.Map.find fid genv.funs with
    | Either.Left fdecl ->
        (fdecl.fun_insts, fdecl.fun_args, fdecl.fun_ret)
    | Right tid ->
        let tdecl = TypeClass.Map.find tid genv.tclass in
        let tc_fdecl = Function.Map.find fid tdecl.tclass_decls in
        ([], tc_fdecl.tc_fun_args, tc_fdecl.tc_fun_ret)
  in
  fprintf ppf "fn %a::%a, %a" Function.pp fid pp_fun_typ fdecl Function.pp fid ;
  List.iter (fprintf ppf " %a" Variable.pp) exp.tfun_vars ;
  fprintf ppf ":@.%a@." pp_texpr exp.tfun_texpr ;
  pp_print_newline ppf ()

let pp_tschema genv ppf schema_impl =
  let sdecl =
    List.find
      (fun sdecl -> sdecl.schema_id = schema_impl.tschema_id)
      (TypeClass.Map.find
         (Schema.typeclass schema_impl.tschema_id)
         genv.tc2schemas )
  in
  fprintf ppf "Schema %a (%a):@." Schema.pp schema_impl.tschema_id pp_schema
    sdecl ;
  Function.Map.iter
    (fun fn e -> pp_tfun genv ppf (fn, e))
    schema_impl.tschema_funs ;
  pp_print_newline ppf ()

let pp_tprog ppf tprog =
  pp_set_geometry ppf ~max_indent:75 ~margin:100 ;
  Schema.Map.iter (fun _ -> pp_tschema tprog.genv ppf) tprog.tschemas ;
  Function.Map.iter (fun fn e -> pp_tfun tprog.genv ppf (fn, e)) tprog.tfuns

let pp_var_pos ppf = function
  | AStackVar i ->
      fprintf ppf "%i(%%rbp)" i
  | AClosVar i ->
      fprintf ppf "%i(%%r12)" i

let pp_arith_op ppf = function
  | SympAst.Add ->
      pp_print_string ppf "+"
  | SympAst.Sub ->
      pp_print_string ppf "-"
  | SympAst.Mul ->
      pp_print_string ppf "*"
  | SympAst.Div ->
      pp_print_string ppf "/"
  | SympAst.Mod ->
      pp_print_string ppf "%"

let pp_bool_op ppf = function
  | SympAst.And ->
      pp_print_string ppf "&&"
  | SympAst.Or ->
      pp_print_string ppf "||"

let pp_compare_op ppf = function
  | SympAst.Equal ->
      pp_print_string ppf "=="
  | SympAst.NotEqual ->
      pp_print_string ppf "/="
  | SympAst.Greater ->
      pp_print_string ppf ">"
  | SympAst.GreaterEqual ->
      pp_print_string ppf ">="
  | SympAst.Lower ->
      pp_print_string ppf "<"
  | SympAst.LowerEqual ->
      pp_print_string ppf "<="

let pp_inst_pos ppf = function
  | AStackInst i ->
      fprintf ppf "%i(%%rbp)" i
  | AClosInst i ->
      fprintf ppf "%i(%%r12)" i
  | AInstInst (i, j) ->
      fprintf ppf "address %i of %i(%%rbp)" j i

let rec pp_alloc_inst ppf = function
  | ALocalInst i ->
      pp_inst_pos ppf i
  | AGlobalInst s ->
      Schema.pp ppf s
  | AGlobalSchema (s, args, _) ->
      fprintf ppf "(@[%a@,with%a@])" Schema.pp s
        (pp_print_list pp_alloc_inst)
        args

let rec pp_aexpr ppf aexpr =
  match aexpr.alloc_expr with
  | AConstant c ->
      fprintf ppf "@[<hv 2>(Constant %a)@]" pp_cst c
  | AVariable v ->
      fprintf ppf "@[<hv 2>(Variable %a)@]" pp_var_pos v
  | ANeg x ->
      fprintf ppf "@[<hv 2>(neg@,%a)@]" pp_aexpr x
  | ANot x ->
      fprintf ppf "@[<hv 2>(not@,%a)@]" pp_aexpr x
  | AArithOp (lhs, op, rhs) ->
      fprintf ppf "@[<hv 2>(%a@,%a@,%a)@]" pp_arith_op op pp_aexpr lhs pp_aexpr
        rhs
  | ABooleanOp (lhs, op, rhs) ->
      fprintf ppf "@[<hv 2>(%a@,%a@,%a)@]" pp_bool_op op pp_aexpr lhs pp_aexpr
        rhs
  | ACompare (lhs, op, rhs) ->
      fprintf ppf "@[<hv 2>(%a@,%a@,%a)@]" pp_compare_op op pp_aexpr lhs
        pp_aexpr rhs
  | AStringConcat (lhs, rhs) ->
      fprintf ppf "@[<hv 2>(concat@,%a@,%a)@]" pp_aexpr lhs pp_aexpr rhs
  | AFunctionCall (f, insts, args) ->
      fprintf ppf "@[<hv 2>(%a@,%a@,%a)@]" Function.pp f
        (pp_print_list pp_alloc_inst)
        insts (pp_print_list pp_aexpr) args
  | AInstanceCall (i, f, args) ->
      fprintf ppf "@[<hv 2>(%a.%a@,%a)@]" pp_alloc_inst i Function.pp f
        (pp_print_list pp_aexpr) args
  | AConstructor (cstr, args) -> (
    match args with
    | [] ->
        Constructor.pp ppf cstr
    | args ->
        fprintf ppf "@[<hv 2>(%a@,%a)@]" Constructor.pp cstr
          (pp_print_list pp_aexpr) args )
  | AIf (cd, tb, fb) ->
      fprintf ppf "@[<hv 2>(if@ %a@,then@ %a@,else@ %a)@]" pp_aexpr cd pp_aexpr
        tb pp_aexpr fb
  | ALocalClosure (l, vars, instl, _) ->
      fprintf ppf "@[<hv 2>(closure of@,@[%a@]@,with@,%a@,and@,%a)@]" Label.pp l
        (pp_print_list pp_inst_pos)
        instl (pp_print_list pp_var_pos) vars
  | ADoEffect e ->
      fprintf ppf "@[<hv 2>(call closure@,%a)@]" pp_aexpr e
  | ALet (v_pos, b, e) ->
      fprintf ppf "@[<hv 2>(let@,@[<hv 2>(%i(%%rbp) = %a)@]@,in %a)@]" v_pos
        pp_aexpr b pp_aexpr e
  | AStringCompareAndBranch d ->
      fprintf ppf
        "@[<hv 2>(compare@ %a@ with@ %s@,\
         @[lower@ %a@]@,\
         @[equal@ %a@]@,\
         @[greater@ %a@])@]" pp_var_pos d.var d.cst pp_aexpr d.lower pp_aexpr
        d.equal pp_aexpr d.greater
  | AIntCompareAndBranch d ->
      fprintf ppf
        "@[<hv 2>(compare@ %a@ with@ %i@,\
         @[lower@ %a@]@,\
         @[equal@ %a@]@,\
         @[greater@ %a@])@]" pp_var_pos d.var d.cst pp_aexpr d.lower pp_aexpr
        d.equal pp_aexpr d.greater
  | AConstructorCase (e, _, c, o) ->
      fprintf ppf "@[<hv 2>(match %a@," pp_var_pos e ;
      Constructor.Map.iter
        (fun c expr ->
          fprintf ppf "@[<hv 2>(%a =>@,%a)@]@," Constructor.pp c pp_aexpr expr
          )
        c ;
      ( match o with
      | Some o ->
          fprintf ppf "@[<hv 2>_ =>@,%a@]" pp_aexpr o
      | None ->
          () ) ;
      fprintf ppf ")@]"
  | AGetField (e, i) ->
      Format.fprintf ppf "@[<hv 2>(field %i of@ %a)@]" i pp_var_pos e

let pp_afun genv ppf aexp =
  let fdecl =
    match Function.Map.find aexp.afun_id genv.funs with
    | Either.Left fdecl ->
        (fdecl.fun_insts, fdecl.fun_args, fdecl.fun_ret)
    | Right tid ->
        let tdecl = TypeClass.Map.find tid genv.tclass in
        let tc_fdecl = Function.Map.find aexp.afun_id tdecl.tclass_decls in
        ([], tc_fdecl.tc_fun_args, tc_fdecl.tc_fun_ret)
  in
  fprintf ppf "fn %a::%a@." Function.pp aexp.afun_id pp_fun_typ fdecl ;
  Seq.iter
    (fun (l, loc_part) ->
      fprintf ppf "%a:@.  @[%a@]@." Label.pp l
        (pp_print_list ~pp_sep:(fun ppf -> pp_force_newline ppf) pp_aexpr)
        loc_part.local_body )
    aexp.afun_annex ;
  fprintf ppf "FunctionBody:@.  @[%a@]@." pp_aexpr aexp.afun_body ;
  pp_print_newline ppf ()

let pp_aschema genv ppf schema_impl =
  let sdecl =
    List.find
      (fun sdecl -> sdecl.schema_id = schema_impl.aschema_id)
      (TypeClass.Map.find
         (Schema.typeclass schema_impl.aschema_id)
         genv.tc2schemas )
  in
  fprintf ppf "Schema %a (%a):@." Schema.pp schema_impl.aschema_id pp_schema
    sdecl ;
  Function.Map.iter
    (fun _ afun -> pp_afun genv ppf afun)
    schema_impl.aschema_funs ;
  pp_print_newline ppf ()

let pp_aprog ppf (aprog : aprogram) =
  pp_set_geometry ppf ~max_indent:75 ~margin:100 ;
  Schema.Map.iter (fun _ -> pp_aschema aprog.aprog_genv ppf) aprog.aschemas ;
  Function.Map.iter (fun _ -> pp_afun aprog.aprog_genv ppf) aprog.afuns

let rec pp_sexpr ppf sexpr =
  match sexpr.symp_expr with
  | SConstant c ->
      fprintf ppf "@[<hv 2>(Constant %a)@]" pp_cst c
  | SVariable v ->
      fprintf ppf "@[<hv 2>(Variable %a)@]" Variable.pp v
  | SNeg x ->
      fprintf ppf "@[<hv 2>(neg@,%a)@]" pp_sexpr x
  | SNot x ->
      fprintf ppf "@[<hv 2>(not@,%a)@]" pp_sexpr x
  | SArithOp (lhs, op, rhs) ->
      fprintf ppf "@[<hv 2>(%a@,%a@,%a)@]" pp_arith_op op pp_sexpr lhs pp_sexpr
        rhs
  | SBooleanOp (lhs, op, rhs) ->
      fprintf ppf "@[<hv 2>(%a@,%a@,%a)@]" pp_bool_op op pp_sexpr lhs pp_sexpr
        rhs
  | SCompare (lhs, op, rhs) ->
      fprintf ppf "@[<hv 2>(%a@,%a@,%a)@]" pp_compare_op op pp_sexpr lhs
        pp_sexpr rhs
  | SStringConcat (lhs, rhs) ->
      fprintf ppf "@[<hv 2>(concat@,%a@,%a)@]" pp_sexpr lhs pp_sexpr rhs
  | SFunctionCall (f, insts, args) ->
      fprintf ppf "@[<hv 2>(%a@,%a@,%a)@]" Function.pp f
        (pp_print_list pp_res_inst)
        insts (pp_print_list pp_sexpr) args
  | SInstanceCall (i, f, args) ->
      fprintf ppf "@[<hv 2>(%a.%a@,%a)@]" pp_res_inst i Function.pp f
        (pp_print_list pp_sexpr) args
  | SConstructor (cstr, args) -> (
    match args with
    | [] ->
        Constructor.pp ppf cstr
    | args ->
        fprintf ppf "@[<hv 2>(%a@,%a)@]" Constructor.pp cstr
          (pp_print_list pp_sexpr) args )
  | SIf (cd, tb, fb) ->
      fprintf ppf "@[<hv 2>(if@ %a@,then@ %a@,else@ %a)@]" pp_sexpr cd pp_sexpr
        tb pp_sexpr fb
  | SBlock l ->
      fprintf ppf "@[<hv 2>(do@.%a)@]" (pp_print_list pp_sexpr) l
  | SLet (v, b, e) ->
      fprintf ppf "@[<hv 2>(let@,@[<hv 2>(%a = %a)@]@,in %a)@]" Variable.pp v
        pp_sexpr b pp_sexpr e
  | SStringCompareAndBranch d ->
      fprintf ppf
        "@[<hv 2>(compare@ %a@ with@ %s@,\
         @[lower@ %a@]@,\
         @[equal@ %a@]@,\
         @[greater@ %a@])@]" Variable.pp d.var d.cst pp_sexpr d.lower pp_sexpr
        d.equal pp_sexpr d.greater
  | SIntCompareAndBranch d ->
      fprintf ppf
        "@[<hv 2>(compare@ %a@ with@ %i@,\
         @[lower@ %a@]@,\
         @[equal@ %a@]@,\
         @[greater@ %a@])@]" Variable.pp d.var d.cst pp_sexpr d.lower pp_sexpr
        d.equal pp_sexpr d.greater
  | SConstructorCase (e, _, c, o) ->
      fprintf ppf "@[<hv 2>(match %a@," Variable.pp e ;
      Constructor.Map.iter
        (fun c expr ->
          fprintf ppf "@[<hv 2>(%a =>@,%a)@]@," Constructor.pp c pp_sexpr expr
          )
        c ;
      ( match o with
      | Some o ->
          fprintf ppf "@[<hv 2>_ =>@,%a@]" pp_sexpr o
      | None ->
          () ) ;
      fprintf ppf ")@]"
  | SGetField (e, i) ->
      Format.fprintf ppf "@[<hv 2>(field %i of@ %a)@]" i Variable.pp e

let pp_sfun genv ppf (fid, sfun) =
  let fdecl =
    match Function.Map.find fid genv.funs with
    | Either.Left fdecl ->
        (fdecl.fun_insts, fdecl.fun_args, fdecl.fun_ret)
    | Right tid ->
        let tdecl = TypeClass.Map.find tid genv.tclass in
        let tc_fdecl = Function.Map.find fid tdecl.tclass_decls in
        ([], tc_fdecl.tc_fun_args, tc_fdecl.tc_fun_ret)
  in
  fprintf ppf "fn %a::%a, %a" Function.pp fid pp_fun_typ fdecl Function.pp fid ;
  List.iter (fprintf ppf " %a" Variable.pp) sfun.sfun_vars ;
  fprintf ppf ":@.%a@." pp_sexpr sfun.sfun_body ;
  pp_print_newline ppf ()

let pp_sschema genv ppf sschema =
  let sdecl =
    List.find
      (fun sdecl -> sdecl.schema_id = sschema.sschema_id)
      (TypeClass.Map.find (Schema.typeclass sschema.sschema_id) genv.tc2schemas)
  in
  fprintf ppf "Schema %a (%a):@." Schema.pp sschema.sschema_id pp_schema sdecl ;
  Function.Map.iter (fun fn e -> pp_sfun genv ppf (fn, e)) sschema.sschema_funs ;
  pp_print_newline ppf ()

let pp_sprog ppf sprog =
  pp_set_geometry ppf ~max_indent:75 ~margin:100 ;
  Schema.Map.iter (fun _ -> pp_sschema sprog.sprog_genv ppf) sprog.sschemas ;
  Function.Map.iter
    (fun fn e -> pp_sfun sprog.sprog_genv ppf (fn, e))
    sprog.sfuns
