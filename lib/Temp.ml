open TAst

let compile_case (e : texpr) (pats : tpattern list) (exprs : texpr list) : texpr
    =
  let rec f (el : texpr list) (pat_mat : (tpattern list * texpr) list) =
    match (el, pat_mat) with
    | _, [] -> raise (Failure "Pattern pas exaustif")
    | [], (_, e) :: _ -> e (* TODO : add warning about useless cases *)
    | _ ->
        let cst_mats, other_mat = assert false in
        let cst_texprs =
          ConstMap.map (fun (el, pat_mat) -> f el pat_mat) cst_mats
        in
        let other_expr =
          match other_mat with
          | Some (other_el, other_pat_mat) -> Some (f other_el other_pat_mat)
          | None -> None
        in
        {
          expr = TContructorCase (assert false, cst_texprs, other_expr);
          expr_typ = assert false;
        }
  in
  f [ e ] (List.map2 (fun p e -> ([ p ], e)) pats exprs)
