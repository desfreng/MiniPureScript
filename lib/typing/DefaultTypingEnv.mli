val unit_t : TypedAst.ttyp

val bool_t : TypedAst.ttyp

val int_t : TypedAst.ttyp

val string_t : TypedAst.ttyp

val effect_t : TypedAst.ttyp -> TypedAst.ttyp

val is_unit_t : TypedAst.ttyp -> bool

val is_bool_t : TypedAst.ttyp -> bool

val is_int_t : TypedAst.ttyp -> bool

val is_string_t : TypedAst.ttyp -> bool

val is_effect_t : TypedAst.ttyp -> bool

val default_genv : TypedAst.global_env

val default_lenv : TypedAst.local_env

val not_fid : TypedAst.Function.t

val mod_fid : TypedAst.Function.t

val log_fid : TypedAst.Function.t

val pure_fid : TypedAst.Function.t

val show_fid : TypedAst.Function.t

val show_bool_sid : Ids.Schema.t

val show_int_sid : Ids.Schema.t
