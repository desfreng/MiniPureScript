include Label
open TypedAst

type avar =
  | ALocalVar of int (* A local variable *)
  | AClosVar of int (* Variable in a closure *)

(** Expression type, with every type possible. *)
type aexpr = {aexpr: aexpr_kind; aexpr_typ: ttyp}

and aexpr_kind =
  | AConstant of Constant.t
  | AVariable of avar
  | ANeg of aexpr
  | ABinOp of aexpr * Ast.binop * aexpr
  | (* "Regular" Function application *)
    AFunctionCall of
      Function.t (* the function id *)
      * resolved_inst list (* the list of instances needed *)
      * aexpr list (* the list of argument *)
  | AFunctionClosure of Function.t * resolved_inst list * aexpr list
  | (* Type-Class Function application *)
    AInstanceCall of
      resolved_inst (* the instance in which the function called is defined *)
      * Function.t (* the function id *)
      * aexpr list (* the list of argument *)
  | AInstanceClosure of resolved_inst * Function.t * aexpr list
  | AConstructor of Constructor.t * aexpr list (* Constructor application *)
  | AIf of aexpr * aexpr * aexpr
  | ALocalClosure of label * avar list
  | ADoEffect of aexpr
  | ALet of avar * aexpr * aexpr
  | AConstantCase of
      aexpr (* The expression we need to compare to each constant *)
      * aexpr Constant.map
      (* The expression to evaluate for each possible constant (of the same type) *)
      * aexpr option (* The expression to evaluate if no constants match *)
  | AContructorCase of
      aexpr (* The expression for which we are looking at the constructor *)
      * aexpr Constructor.map
      (* The expression to evaluate for each possible constructor *)
      * aexpr option (* The expression to evaluate if no constructor match *)
  | AGetField of aexpr * int
(* Retrieve one of the expression of a symbol constructor *)

(** Describe the implementation of a function *)
type afun =
  { afun_id: Function.t
        (* id of the function implemented *)

        (* ; fun_impl_vars: Variable.t list (* argument of the function, in order *) *)
  ; afun_arity: int (* number of argument *)
  ; afun_body: (aexpr * label) option
        (* body of the function with its label, None if builtins *)
  ; afun_annex: aexpr list LabelMap.t }

type aschema =
  { aschema_id: Schema.t (* id of the shema implemented *)
  ; aschema_funs: afun Function.map
        (* maps each function defined in this schema to its allocated implementation. *)
  }

type aprogram =
  { afuns: afun Function.map
        (* maps each "normal" function definition to its implementation *)
  ; aschemas: aschema Schema.map (* maps each schema to its implementation *)
  ; genv: global_env (* The resulting typing environment. *)
  ; main:
      Function.t * label (* id of the program entry point with it's label. *) }

let word_size = 8

let initial_fp = -word_size

let call_stack_size = 16
