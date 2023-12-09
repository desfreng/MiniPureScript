%{
open Ast

let split_typ_list =
  let rec f acc = function
    | [] -> assert false
    | [a] -> List.rev acc, a
    | hd::tl -> f (hd::acc) tl
  in f []

let mk_ast v pos =
  let beg_pos = lexloc_to_pos pos in
  let pos = merge_pos beg_pos (PostLexer.last_pos_emmited ()) in
  { v; pos }

%}

%start file

%type <program> file

%%
// A simple symbol, used to check the value of the UIndent  (see `file` symbol)
%inline uindent_text: t=UINDENT { (t, lexloc_to_pos $loc) }

file:
"module" m=uindent_text "where" "{" imports d=separated_nonempty_list(";", decls) "}" EOF { assert_text_is m "Main"; d }

imports:
"import" p=uindent_text ";"
"import" ef=uindent_text ";"
"import" efc=uindent_text ";" { assert_text_is p   "Prelude";
                                assert_text_is ef  "Effect";
                                assert_text_is efc "Effect.Console" }
decls:
| f=defn    { f }
| t=tdecl   { t }
| "data" t=UINDENT arg=LINDENT* "=" l=separated_nonempty_list("|", constr_def)
    { mk_ast (Data (t, arg, l)) $loc }

| "class" c=UINDENT arg=LINDENT* "where" "{" l=separated_list(";", tdecl) "}"
    { mk_ast (Class (c, arg, l)) $loc }

| "instance" i=instance "where" "{" l=separated_list(";", defn) "}"
    { mk_ast (Instance (i, l)) $loc }

%inline constr_def: c=UINDENT arg=atype* { (c, arg) }

defn: f=LINDENT p=patarg* "=" e=expr
    { mk_ast (FunDecl (f, p, e)) $loc }

tdecl:
| f=LINDENT "::" t=separated_nonempty_list("->", typ)
    { let arg, ret = split_typ_list t in
        mk_ast (TypeDecl (f, [], [], arg, ret)) $loc }

| f=LINDENT "::" "forall" l=LINDENT+ "." t=separated_nonempty_list("->", typ)
    { let arg, ret = split_typ_list t in
        mk_ast (TypeDecl (f, l, [], arg, ret)) $loc }

| f=LINDENT "::" c=class_list t=separated_nonempty_list("->", typ)
    { let arg, ret = split_typ_list t in
        mk_ast (TypeDecl (f, [], c, arg, ret)) $loc }

| f=LINDENT "::" "forall" l=LINDENT+ "." c=class_list t=separated_nonempty_list("->", typ)
    { let arg, ret = split_typ_list t in
        mk_ast (TypeDecl (f, l, c, arg, ret)) $loc }


class_list:
| v=cio_decl "=>"                  { [v] }
| l=class_list v=cio_decl "=>"     { v::l }


instance:
| r=cio_decl
    { ([], r) }

| a=cio_decl "=>" r=cio_decl
    { ([a], r) }

| "(" l=separated_nonempty_list(",", cio_decl) ")" "=>" r=cio_decl
    { (l, r) }

cio_decl:
| cstr=UINDENT arg=atype*
    { mk_ast (CoI_Decl (cstr, arg)) $loc }

atype:
| c=UINDENT         { mk_ast (AstTData (c, [])) $loc }
| t=non_const_type  { t }

typ:
| t=non_const_type
    { t }
| cstr=UINDENT arg=atype*
    { mk_ast (AstTData (cstr, arg)) $loc }

non_const_type:
| v=LINDENT         { mk_ast (AstTVar v) $loc }
| "(" t=typ ")"     { t }


pattern:
| p=patarg            { p }
| c=UINDENT arg=patarg+
                      { mk_ast (PatConstructor (c, arg)) $loc }


patarg:
| c=constant          { mk_ast (PatConstant c) $loc }
| v=LINDENT           { mk_ast (PatVariable v) $loc }
// An Uindent can only be a "zeroary" Constructor
// because we have no record in MiniPureScript
| c=UINDENT           { mk_ast (PatConstructor (c, [])) $loc }
| "(" p=pattern ")"   { p }


constant:
| "true"      { mk_ast (True) $loc }
| "false"     { mk_ast (False) $loc }
| i=INT_CST   { mk_ast (Int i) $loc }
| s=STR_CST   { mk_ast (Str s) $loc }


atom:
| c=constant                { mk_ast (ExprConstant c) $loc }
| v=LINDENT                 { mk_ast (ExprVar v) $loc }
// An Uindent can only be a "zeroary" Constructor
// because we have no record in MiniPureScript
| c=UINDENT                 { mk_ast (AppConstr (c, [])) $loc }
| "(" e=expr ")"            { e }
| "(" e=expr "::" t=typ ")" { mk_ast (WithType (e, t)) $loc }


expr:
| a=atom
    { a }

| "-" e=expr
    { mk_ast (Neg e) $loc } %prec U_MINUS

| l=expr op=binop r=expr
    { mk_ast (BinOp (l, op, r)) $loc }

| f=LINDENT arg=atom+
    { mk_ast (AppFun (f, arg)) $loc }

| f=UINDENT arg=atom+
    { mk_ast (AppConstr (f, arg)) $loc }

| "if" c=expr "then" tb=expr "else" tf=expr
    { mk_ast (If (c, tb, tf)) $loc }

| "do" "{" l=separated_nonempty_list(";", expr) "}"
    { mk_ast (Block l) $loc }

| "let" "{" bl=separated_nonempty_list(";", binding) "}" "in" e=expr
    { mk_ast (Let (bl, e)) $loc }

| "case" e=expr "of" "{" bl=separated_nonempty_list(";", branch) "}"
    { mk_ast (Case (e, bl)) $loc }


%inline binding: v=LINDENT "=" e=expr{ (v, e) }
%inline branch: p=pattern "->" e=expr { (p, e) }

%inline binop:
| "=="  { Eq }
| "/="  { Neq }
| ">"   { Gt }
| ">="  { Ge }
| "<"   { Lt }
| "<="  { Le }
| "+"   { Plus }
| "-"   { Minus }
| "*"   { Mul }
| "/"   { Div }
| "<>"  { Concat }
| "&&"  { And }
| "||"  { Or }

%%
