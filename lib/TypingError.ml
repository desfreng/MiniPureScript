open TAst
open Ast

exception TypeError of string * position

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
          Format.pp_print_string ppf sid
      | TSymbol (sid, args) when fst ->
          Format.pp_print_string ppf sid ;
          List.iter (Format.fprintf ppf " %a" (pp false)) args
      | TSymbol (sid, args) ->
          Format.fprintf ppf "(%s" sid ;
          List.iter (Format.fprintf ppf " %a" (pp false)) args ;
          Format.pp_print_string ppf ")"
    in
    pp (not atomic) ppf t

let setup_pp_inst lenv t =
  let pp =
    List.fold_left (fun acc (TInstance (_, ttyps)) -> ttyps @ acc) [] t
    |> setup_pp_ttyp ~atomic:true lenv
  in
  fun ppf inst ->
    let (TInstance (cn, inst_ttyp)) = inst in
    Format.pp_print_string ppf cn ;
    List.iter (Format.fprintf ppf " %a" pp) inst_ttyp

let rec pp_pat ppf p =
  match p.pat with
  | TPatWildcard ->
      Format.pp_print_string ppf "_"
  | TPatVar _ ->
      Format.pp_print_string ppf "var"
  | TPatConstant TUnitConstant ->
      Format.pp_print_string ppf "unit"
  | TPatConstant (TBoolConstant f) ->
      Format.pp_print_bool ppf f
  | TPatConstant (TIntConstant i) ->
      Format.pp_print_int ppf i
  | TPatConstant (TStringConstant s) ->
      Format.pp_print_string ppf s
  | TPatConstructor (cstr, args) ->
      Format.fprintf ppf "(%s" cstr ;
      List.iter (Format.fprintf ppf " %a" pp_pat) args ;
      Format.fprintf ppf ")"

let rec pp_list pp ppf = function
  | [] ->
      ()
  | hd :: tl ->
      Format.fprintf ppf "%a, " pp hd ;
      pp_list pp ppf tl

let unknown_type_var n pos =
  let txt =
    Format.sprintf "The type variable '%s' is not defined is this declaration."
      n
  in
  raise (TypeError (txt, pos.pos))

let unknown_symbol n pos =
  let txt =
    Format.sprintf "The type symbol '%s' is not defined in this declaration." n
  in
  raise (TypeError (txt, pos.pos))

let symbol_arity_mismatch decl ar_found pos =
  let txt =
    Format.sprintf
      "The type symbol '%s' expects %i arguments, but is applied here to %i \
       arguments."
      decl.symbid decl.arity ar_found
  in
  raise (TypeError (txt, pos.pos))

let invalid_anonymous pos =
  let txt = "Wildcard '_' not expected here." in
  raise (TypeError (txt, pos.pos))

let variable_not_declared n pos =
  let txt =
    Format.sprintf "The variable '%s' is not defined in this expression." n
  in
  raise (TypeError (txt, pos.pos))

let expected_type_in lenv found expected_list pos =
  let pp = setup_pp_ttyp lenv (found :: expected_list) in
  let rec _pp ppf = function
    | [] ->
        assert false
    | [x] ->
        pp ppf x
    | [x; y] ->
        Format.fprintf ppf "%a or %a." pp x pp y
    | hd :: tl ->
        Format.fprintf ppf "%a, %a" pp hd _pp tl
  in
  let txt =
    Format.asprintf
      "This expression is of type %a. However, one of the following types is \
       expected here: %a"
      pp found _pp expected_list
  in
  raise (TypeError (txt, pos.pos))

(** An error occured during the unification of [t1] and [t2]. *)
let unification_error lenv uerr t1 t2 pos =
  let txt =
    match uerr with
    | SymbolMismatch v ->
        let pp = setup_pp_ttyp lenv [t1; t2] in
        Format.asprintf
          "Impossible to match type %a with type %a, type symbols '%s' and \
           '%s' are different."
          pp t1 pp t2 v.symb1 v.symb2
    | NotSameTypes v ->
        let pp = setup_pp_ttyp lenv [t1; t2; v.t1; v.t2] in
        Format.asprintf
          "Impossible to match type %a with type %a, the type %a is different \
           from the type %a."
          pp t1 pp t2 pp v.t1 pp v.t2
    | VariableOccuring v ->
        let pp = setup_pp_ttyp lenv [t1; t2; v.var; v.typ] in
        Format.asprintf
          "Unable to match type %a with type %a, variable of type %a appears \
           in type %a."
          pp t1 pp t2 pp v.var pp v.typ
  in
  raise (TypeError (txt, pos.pos))

let constr_arity_mismatch constr expected found pos =
  let txt =
    Format.sprintf
      "The constructor '%s' expects %i arguments, but is applied here to %i \
       arguments."
      constr expected found
  in
  raise (TypeError (txt, pos.pos))

let unknown_constructor n pos =
  let txt =
    Format.sprintf "The constructor '%s' is not defined in this expression." n
  in
  raise (TypeError (txt, pos.pos))

let same_variable_in_pat n pos =
  let txt =
    Format.sprintf
      "The variable '%s' is tied to several values in this case expression." n
  in
  raise (TypeError (txt, pos.pos))

let variable_not_a_function lenv var_name typ ex_arity pos =
  let pp = setup_pp_ttyp lenv [typ] in
  let txt =
    Format.asprintf
      "The variable '%s' of type %a cannot be interpreted as a function with \
       %i arguments."
      var_name pp typ ex_arity
  in
  raise (TypeError (txt, pos.pos))

let unknown_function n pos =
  let txt =
    Format.sprintf "The function '%s' is not defined in this expression." n
  in
  raise (TypeError (txt, pos.pos))

let function_arity_mismatch fname expected found pos =
  let txt =
    Format.sprintf
      "The function '%s' expects %i arguments, but is applied here to %i \
       arguments."
      fname expected found
  in
  raise (TypeError (txt, pos.pos))

let unresolved_instance lenv inst stack pos =
  let pp = setup_pp_inst lenv (inst :: stack) in
  let rec pp_l ppf = function
    | [] ->
        ()
    | hd :: tl ->
        Format.fprintf ppf "While solving requirement of %a.@." pp hd ;
        pp_l ppf tl
  in
  let txt =
    if stack <> [] then
      Format.asprintf
        "The instance '%a' cannot be resolved in the current environment.@.@.%a"
        pp inst pp_l stack
    else
      Format.asprintf
        "The instance '%a' cannot be resolved in the current environment." pp
        inst
  in
  raise (TypeError (txt, pos.pos))

let typ_var_already_decl_in_symb var symbol pos =
  let txt =
    Format.sprintf
      "The type variable '%s' appear several times in the declaration of the \
       type symbol '%s'."
      var symbol
  in
  raise (TypeError (txt, pos.pos))

let symbol_already_exists symbol pos =
  let txt =
    Format.sprintf "The type symbol '%s' is declared several times." symbol
  in
  raise (TypeError (txt, pos.pos))

let constr_already_in_symb constr symbol pos =
  let txt =
    Format.sprintf
      "The constructor '%s' is defined several times in the declaration of the \
       type symbol '%s'."
      constr symbol
  in
  raise (TypeError (txt, pos.pos))

let constr_already_in_genv constr symdecl pos =
  let txt =
    Format.sprintf
      "The constructor '%s' is already declared within the type symbol '%s'."
      constr symdecl.symbid
  in
  raise (TypeError (txt, pos.pos))

let function_already_exists fun_name pos =
  let txt =
    Format.sprintf "The function '%s' is declared several times." fun_name
  in
  raise (TypeError (txt, pos.pos))

let class_already_exists class_name pos =
  let txt =
    Format.sprintf "The type class '%s' is declared several times." class_name
  in
  raise (TypeError (txt, pos.pos))

let typ_var_already_decl_in_class var class_name pos =
  let txt =
    Format.sprintf
      "The type variable '%s' appear several times in the declaration of the \
       type class '%s'."
      var class_name
  in
  raise (TypeError (txt, pos.pos))

let no_qvar_in_class_fun_decl fun_name class_name pos =
  let txt =
    Format.sprintf
      "The function '%s' in the type class '%s' is declared with quantified \
       types variables."
      fun_name class_name
  in
  raise (TypeError (txt, pos.pos))

let no_instl_in_class_fun_decl fun_name class_name pos =
  let txt =
    Format.sprintf
      "The function '%s' of the type class '%s' is declared with type class \
       constraints."
      fun_name class_name
  in
  raise (TypeError (txt, pos.pos))

let missing_fun_type_decl fun_name pos =
  let txt =
    Format.sprintf "Missing type declaration of function '%s'." fun_name
  in
  raise (TypeError (txt, pos.pos))

let typ_var_already_decl_in_fun var fun_name pos =
  let txt =
    Format.sprintf
      "The type variable '%s' appear several times in the declaration of the \
       function '%s'."
      var fun_name
  in
  raise (TypeError (txt, pos.pos))

let unknown_class n pos =
  let txt = Format.sprintf "The type class '%s' is not defined." n in
  raise (TypeError (txt, pos.pos))

let class_arity_mismatch class_decl ar_found pos =
  let txt =
    Format.sprintf
      "The type class '%s' expects %i arguments, but is applied here to %i \
       arguments."
      class_decl.class_name class_decl.carity ar_found
  in
  raise (TypeError (txt, pos.pos))

let same_variable_in_fun var_name fun_name pos =
  let txt =
    Format.sprintf
      "The variable '%s' is tied to several values in this implementation of \
       the function '%s'."
      var_name fun_name
  in
  raise (TypeError (txt, pos.pos))

let multiples_non_var_in_fun_args fun_name pos =
  let txt =
    Format.sprintf
      "Several filter patterns that are not variables appear in this \
       implementation of the function '%s'."
      fun_name
  in
  raise (TypeError (txt, pos.pos))

let strange_non_var_in_decls fun_name pos =
  let txt =
    Format.sprintf
      "Not all implementations of the function '%s' have their filter patterns \
       on the same argument."
      fun_name
  in
  raise (TypeError (txt, pos.pos))

let missing_fun_impl fun_name pos =
  let txt = Format.sprintf "The function '%s' is not implemented." fun_name in
  raise (TypeError (txt, pos.pos))

let not_exhaustive_case pos =
  raise (TypeError ("This pattern matching is not exhaustive.", pos.pos))

let not_exhaustive_fun fname (pos : Ast.decl list) =
  let fst = List.hd pos in
  let lst = List.rev pos |> List.hd in
  let pos =
    {fst.pos with end_line= lst.pos.end_line; end_col= lst.pos.end_col}
  in
  let txt =
    Format.sprintf
      "Pattern matching on the arguments of the function '%s' is not \
       exhaustive."
      fname
  in
  raise (TypeError (txt, pos))

let multiple_const_def cstname pos =
  let txt =
    Format.sprintf "The global constant '%s' is defined several times." cstname
  in
  raise (TypeError (txt, pos.pos))

let missing_main pos =
  let lst = List.rev pos |> List.hd in
  raise
    (TypeError
       ("Missing declaration and implementation of the function main.", lst.pos)
    )

let same_fun_in_class fun_name class_name pos =
  let txt =
    Format.sprintf
      "The function '%s' is defined several times in the type class '%s'."
      fun_name class_name
  in
  raise (TypeError (txt, pos.pos))

let can_unify_instances lenv prod_inst sdecl pos =
  let pp = setup_pp_inst lenv [prod_inst; sdecl.prod] in
  let txt =
    Format.asprintf "Instances '%a' and '%a' can be unified." pp prod_inst pp
      sdecl.prod
  in
  raise (TypeError (txt, pos.pos))

let function_already_def_in_inst lenv fname inst pos =
  let pp = setup_pp_inst lenv [inst] in
  let txt =
    Format.asprintf
      "The function '%s' is implemented several times within the instance '%a'."
      fname pp inst
  in
  raise (TypeError (txt, pos.pos))

let function_not_in_class fname class_decl pos =
  let txt =
    Format.sprintf "The function '%s' is not defined in the type class '%s'."
      fname class_decl.class_name
  in
  raise (TypeError (txt, pos.pos))

let missing_functions lenv inst fdone class_decl pos =
  let miss_fun =
    SMap.filter (fun name _ -> SSet.mem name fdone) class_decl.cfun_decls
  in
  let rec _pp ppf = function
    | [] ->
        assert false
    | [x] ->
        Format.pp_print_string ppf x
    | [x; y] ->
        Format.fprintf ppf "%s and %s" x y
    | hd :: tl ->
        Format.fprintf ppf "%s, %a" hd _pp tl
  in
  let pp = setup_pp_inst lenv [inst] in
  let txt =
    Format.asprintf
      "The '%a' instance is missing the implementation of the functions %a \
       declared in the '%s' type class."
      pp inst _pp
      (SMap.bindings miss_fun |> List.map fst)
      class_decl.class_name
  in
  raise (TypeError (txt, pos.pos))
