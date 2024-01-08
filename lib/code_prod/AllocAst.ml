include Label
include SympAst

type var_position =
  | ALocalVar of int (* A local variable *)
  | AClosVar of int (* Variable in a closure *)

type direct_value = FromMemory of var_position | FromConstant of Constant.t

(** Expression type, with every type possible. *)
type alloc_expr = {alloc_expr: alloc_expr_kind; alloc_expr_typ: ttyp}

and alloc_expr_kind =
  | AConstant of Constant.t (* A constant *)
  | AVariable of var_position (* A variable *)
  | ANeg of alloc_expr (* The opposite of an expression *)
  | ANot of alloc_expr (* The boolean negation of an expression *)
  | AArithOp of alloc_expr * arith_op * alloc_expr (* An arithmetic operation *)
  | ABooleanOp of alloc_expr * bool_op * alloc_expr (* A boolean operation *)
  | ACompare of alloc_expr * comp_op * alloc_expr (* A comparaison *)
  | AStringConcat of
      alloc_expr * alloc_expr (* The concatenation of two strings *)
  | (* "Regular" Function application *)
    AFunctionCall of
      Function.t (* the function id *)
      * resolved_inst list (* the list of instances needed *)
      * direct_value list (* the list of argument *)
  | (* Type-Class Function application *)
    AInstanceCall of
      resolved_inst (* the instance in which the function called is defined *)
      * Function.t (* the function id *)
      * direct_value list (* the list of argument *)
  | AConstructor of
      Constructor.t * direct_value list (* Constructor application *)
  | AIf of alloc_expr * alloc_expr * alloc_expr (* A conditional branchment *)
  | ALocalClosure of label * var_position list
  | ADoEffect of alloc_expr
  | ALet of
      var_position * alloc_expr * alloc_expr (* Definition of a variable *)
  | ACompareAndBranch of
      { lhs: var_position
            (** The variable refering to value filtered by the constants *)
      ; rhs: Constant.t  (** The constant we compare the expression *)
      ; lower: alloc_expr  (** if expr < const, we execute this branch *)
      ; equal: alloc_expr  (** if expr = const, we execute this branch *)
      ; greater: alloc_expr  (** if expr > const, we execute this branch *) }
  | AContructorCase of
      var_position
      * ttyp (* The variable refering to value filtered by the constructors *)
      * alloc_expr Constructor.map
      (* The expression to evaluate for each possible constructor *)
      * alloc_expr option
    (* The expression to evaluate if no constructor match *)
  | AGetField of var_position * ttyp * int
(* Retrieve one of the expression of a symbol constructor *)

type local_afun_part =
  { local_body: alloc_expr list (* The list of side-effect performed *)
  ; local_stack_reserved: int
        (* the space required in order to store the value
           of each local variable *) }

(** Describe the implementation of a function *)
type afun =
  { afun_id: Function.t (* id of the function implemented *)
  ; afun_arity: int (* number of argument *)
  ; afun_stack_reserved: int
        (* the space required in order to store the value
           of each local variable of the function. *)
  ; afun_body: alloc_expr (* body of the function *)
  ; afun_annex: (label * local_afun_part) Seq.t
        (* The list of all blocks of the function defining
           a side effect closure. *) }

type aschema =
  { aschema_id: Schema.t (* id of the shema implemented *)
  ; aschema_funs: afun Function.map
        (* maps each function defined in this schema to its allocated implementation. *)
  ; aschema_label: label Function.map
        (* maps each function defined in this schema to its label. *) }

type aprogram =
  { afuns: afun Function.map
        (* maps each "normal" function definition to its implementation *)
  ; afuns_labels: label Function.map (* maps function to its label *)
  ; aschemas: aschema Schema.map (* maps each schema to its implementation *)
  ; aprog_genv: global_env (* The resulting typing environment. *)
  ; aprog_main: Function.t (* id of the program entry point. *) }
