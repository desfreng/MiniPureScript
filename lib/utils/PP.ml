open TAst
open Format

let pp_cst ppf = function
  | Constant.TBool b ->
      pp_print_bool ppf b
  | Constant.TInt i ->
      pp_print_int ppf i
  | Constant.TString s ->
      pp_print_string ppf s
  | Constant.TUnit ->
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
  | ArgumentInstance i ->
      fprintf ppf "(Instance Argument %d)" i
  | GlobalInstance _ ->
      fprintf ppf "(Instance %d)" 0
  | GlobalSchema (_, args) ->
      fprintf ppf "@[<hv 2>(Schema %d" 0 ;
      List.iter (fprintf ppf "@;%a" pp_res_inst) args ;
      fprintf ppf ")@]"

let rec pp ppf e =
  match e.expr with
  | TConstant c ->
      fprintf ppf "@[<hv 2>(Constant %a)@]" pp_cst c
  | TVariable v ->
      fprintf ppf "@[<hv 2>(Variable %a)@]" Variable.pp v
  | TNeg x ->
      fprintf ppf "@[<hv 2>(neg@;%a)@]" pp x
  | TBinOp (lhs, op, rhs) ->
      fprintf ppf "@[<hv 2>(%a@;%a@;%a)@]" pp_binop op pp lhs pp rhs
  | TRegularFunApp (f, insts, args) ->
      fprintf ppf "@[<hv 2>(%a" Function.pp f ;
      List.iter (fun i -> fprintf ppf "@;%a" pp_res_inst (Lazy.force i)) insts ;
      List.iter (fprintf ppf "@;%a" pp) args ;
      fprintf ppf ") @]"
  | TTypeClassFunApp (i, f, args) ->
      fprintf ppf "@[<hv 2>(%a.%a" pp_res_inst (Lazy.force i) Function.pp f ;
      List.iter (fprintf ppf "@;%a" pp) args ;
      fprintf ppf ")@]"
  | TConstructor (cstr, args) -> (
    match args with
    | [] ->
        Constructor.pp ppf cstr
    | args ->
        fprintf ppf "@[<hv 2>(%a" Constructor.pp cstr ;
        List.iter (fprintf ppf "@;%a" pp) args ;
        fprintf ppf ")@]" )
  | TIf (cd, tb, fb) ->
      fprintf ppf "@[<hv 2>(if@ %a@;then@ %a@;else@ %a)@]" pp cd pp tb pp fb
  | TBlock l ->
      fprintf ppf "@[<hv 2>(do" ;
      List.iter (fprintf ppf "@;%a" pp) l ;
      fprintf ppf ")@]"
  | TLet (v, b, e) ->
      fprintf ppf "@[<hv 2>(let@;@[<hv 2>(%a = %a)@]@;in %a)@]" Variable.pp v pp
        b pp e
  | TConstantCase (e, c, o) ->
      fprintf ppf "@[<hv 2>(match %a@," pp e ;
      Constant.Map.iter
        (fun c expr -> fprintf ppf "@[<hv 2>(%a =>@;%a)@]@," pp_cst c pp expr)
        c ;
      ( match o with
      | Some o ->
          fprintf ppf "@[<hv 2>_ =>@;%a@]" pp o
      | None ->
          () ) ;
      fprintf ppf ")@]"
  | TContructorCase (e, c, o) ->
      fprintf ppf "@[<hv 2>(match %a@," pp e ;
      Constructor.Map.iter
        (fun c expr ->
          fprintf ppf "@[<hv 2>(%a =>@;%a)@]@," Constructor.pp c pp expr )
        c ;
      ( match o with
      | Some o ->
          fprintf ppf "@[<hv 2>_ =>@;%a@]" pp o
      | None ->
          () ) ;
      fprintf ppf ")@]"
  | TGetField (e, i) ->
      Format.fprintf ppf "@[<hv 2>(field %i of@ %a)@]" i pp e

let pp_prog ppf tprog =
  pp_set_geometry ppf ~max_indent:75 ~margin:100 ;
  Function.Map.iter
    (fun fn e ->
      fprintf ppf "fn %a" Function.pp fn ;
      List.iter (fprintf ppf " %a" Variable.pp) e.fun_impl_vars ;
      fprintf ppf " :@.%a@.@." pp e.fun_impl_expr )
    tprog.funs_impl
