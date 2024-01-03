val unit_t : TAst.ttyp

val bool_t : TAst.ttyp

val int_t : TAst.ttyp

val string_t : TAst.ttyp

val effect_t : TAst.ttyp -> TAst.ttyp

val default_genv : TAst.global_env

val default_lenv : TAst.local_env

val is_unit_t : TAst.ttyp -> bool

val is_bool_t : TAst.ttyp -> bool

val is_int_t : TAst.ttyp -> bool

val is_string_t : TAst.ttyp -> bool

val is_effect_t : TAst.ttyp -> bool
