include TypedAst

type arith_op = Add | Sub | Mul | Div | Mod

type bool_op = And | Or

type comp_op = Equal | NotEqual | Greater | GreaterEqual | Lower | LowerEqual

(** Expression type, with every type possible. *)
type symp_expr = {symp_expr: symp_expr_kind; symp_expr_typ: ttyp}

and symp_expr_kind =
  | SConstant of Constant.t (* A constant *)
  | SVariable of Variable.t (* A variable *)
  | SNeg of symp_expr (* The opposite of an expression *)
  | SNot of symp_expr (* The boolean negation of an expression *)
  | SArithOp of symp_expr * arith_op * symp_expr (* An arithmetic operation *)
  | SBooleanOp of symp_expr * bool_op * symp_expr (* A boolean operation *)
  | SCompare of symp_expr * comp_op * symp_expr (* A comparaison *)
  | SStringConcat of
      symp_expr * symp_expr (* The concatenation of two strings *)
  | SFunctionCall of
      Function.t (* the function id *)
      * resolved_inst list (* the list of instances needed *)
      * (Variable.t, Constant.t) Either.t list (* the list of arguments *)
  | SInstanceCall of
      resolved_inst (* the instance in which the function called is defined *)
      * Function.t (* the function id *)
      * (Variable.t, Constant.t) Either.t list (* the list of arguments *)
  | SConstructor of
      Constructor.t
      * (Variable.t, Constant.t) Either.t list (* Constructor application *)
  | SIf of symp_expr * symp_expr * symp_expr (* A conditional branchment *)
  | SBlock of symp_expr list (* A block of effect *)
  | SLet of Variable.t * symp_expr * symp_expr (* Definition of a variable *)
  | SCompareAndBranch of
      { lhs: Variable.t
            (** The variable refering to value filtered by the constants *)
      ; rhs: Constant.t  (** The constant we compare the expression *)
      ; lower: symp_expr  (** if expr < const, we execute this branch *)
      ; equal: symp_expr  (** if expr = const, we execute this branch *)
      ; greater: symp_expr  (** if expr > const, we execute this branch *) }
  | SContructorCase of
      Variable.t
      * ttyp (* The variable refering to value filtered by the constructors *)
      * symp_expr Constructor.map
      (* The expression to evaluate for each possible constructor *)
      * symp_expr option
    (* The expression to evaluate if no constructor match *)
  | SGetField of Variable.t * ttyp * int
(* Retrieve one of the expression of a symbol constructor *)

(** Describe the implementation of a function *)
type sfun =
  { sfun_id: Function.t
  ; sfun_vars: Variable.t list (* argument of the function, in order *)
  ; sfun_arity: int (* number of argument *)
  ; sfun_body: symp_expr (* body of the function *) }

type sschema =
  { sschema_id: Schema.t (* id of the shema implemented *)
  ; sschema_funs: sfun Function.map
        (* maps each function defined in this schema to its allocated implementation. *)
  }

type sprogram =
  { sfuns: sfun Function.map
        (* maps each "normal" function definition to its implementation *)
  ; sschemas: sschema Schema.map (* maps each schema to its implementation *)
  ; sprog_genv: global_env (* The resulting typing environment *)
  ; sprog_main: Function.t (* id of the program entry point *) }
