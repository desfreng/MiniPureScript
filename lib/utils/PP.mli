val setup_pp_ttyp :
     ?atomic:bool
  -> TypedAst.local_env
  -> TypedAst.ttyp list
  -> Format.formatter
  -> TypedAst.ttyp
  -> unit

val setup_pp_inst :
     TypedAst.local_env
  -> (TypedAst.TypeClass.t * TypedAst.ttyp list) list
  -> Format.formatter
  -> TypedAst.TypeClass.t * TypedAst.ttyp list
  -> unit

val pp_tprog : Format.formatter -> TypedAst.tprogram -> unit

val pp_sprog : Format.formatter -> SympAst.sprogram -> unit

val pp_aprog : Format.formatter -> AllocAst.aprogram -> unit
