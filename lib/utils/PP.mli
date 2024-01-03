val pp_cst : Format.formatter -> TAst.Constant.t -> unit

val pp_binop : Format.formatter -> Ast.binop -> unit

val pp_res_inst : Format.formatter -> TAst.res_inst_kind -> unit

val pp : Format.formatter -> TAst.texpr -> unit

val pp_prog : Format.formatter -> TAst.tprogram -> unit
