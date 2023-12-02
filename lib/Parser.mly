%{
open Ast

let split_typ_list =
  let rec f acc = function
    | [] -> assert false
    | [a] -> acc, a
    | hd::tl -> f (hd::acc) tl
  in f []

%}

%token EOF

// Keywords
%token CASE                 "case"
%token CLASS                "class"
%token DATA                 "data"
%token DO                   "do"
%token ELSE                 "else"
%token FALSE                "false"
%token FORALL               "forall"
%token IF                   "if"
%token IMPORT               "import"
%token IN                   "in"
%token INSTANCE             "instance"
%token LET                  "let"
%token MODULE               "module"
%token OF                   "of"
%token THEN                 "then"
%token TRUE                 "true"
%token WHERE                "where"

// Tokens with data
%token <string> LINDENT
%token <string> UINDENT
%token <string> STR_CST
%token <int> INT_CST

// Expressions
%token LPAR                 "("
%token RPAR                 ")"
%token EQ_SIGN              "="

// Operators
%token EQ                   "=="
%token NOT_EQ               "/="
%token LT                   "<"
%token LE                   "<="
%token GT                   ">"
%token GE                   ">="
%token PLUS                 "+"
%token MINUS                "-"
%token MUL                  "*"
%token DIV                  "/"
%token CONCAT               "<>"
%token AND                  "&&"
%token OR                   "||"

// Typing
%token ARROW                "->"
%token EQRARROW             "=>"
%token DOUBLECOLON          "::"
%token PERIOD               "."
%token COMMA                ","
%token PIPE                 "|"

// Code blocks
%token LACC                 "{"
%token RACC                 "}"
%token SEMICOLON            ";"


// Precedences

%nonassoc "in" "else"
%left "||"
%left "&&"
%nonassoc "==" "/=" ">" ">=" "<" "<="
%left "+" "-" "<>"
%left "*" "/"
%nonassoc U_MINUS

%start file

%type <program> file

%%
// A simple symbol, used to check the value of the UIndent  (see `file` symbol)
%inline uindent_text: t=UINDENT { (t, $startpos, $endpos) }

file:
"module" m=uindent_text "where" "{" imports d=separated_nonempty_list(";", decls) "}" EOF { ParserError.assert_text_is m "Main"; d }

imports:
"import" p=uindent_text ";"
"import" ef=uindent_text ";"
"import" efc=uindent_text ";" { ParserError.assert_text_is p   "Prelude";
                                ParserError.assert_text_is ef  "Effect";
                                ParserError.assert_text_is efc "Effect.Console" }
decls:
| f=defn    { f }
| t=tdecl   { t }
| "data" t=UINDENT arg=LINDENT* "=" l=separated_nonempty_list("|", constr_def)
    { { v=Data (t, arg, l); beg_pos=$startpos; end_pos=$endpos; } }

| "class" c=UINDENT arg=LINDENT* "where" "{" l=separated_list(";", tdecl) "}"
    { { v=Class (c, arg, l); beg_pos=$startpos; end_pos=$endpos; } }

| "instance" i=instance "where" "{" l=separated_list(";", defn) "}"
    { { v=Instance (i, l); beg_pos=$startpos; end_pos=$endpos; } }

%inline constr_def: c=UINDENT arg=atype* { (c, arg) }

defn: f=LINDENT p=patarg* "=" e=expr
    { { v=FunDecl (f, p, e); beg_pos=$startpos; end_pos=$endpos; } }

tdecl:
| f=LINDENT "::" t=separated_nonempty_list("->", typ)
    { let arg, ret = split_typ_list t in
        { v=TypeDecl (f, [], [], arg, ret); beg_pos=$startpos; end_pos=$endpos; } }

| f=LINDENT "::" "forall" l=LINDENT+ "." t=separated_nonempty_list("->", typ)
    { let arg, ret = split_typ_list t in
        { v=TypeDecl (f, l, [], arg, ret); beg_pos=$startpos; end_pos=$endpos; } }

| f=LINDENT "::" c=class_list t=separated_nonempty_list("->", typ)
    { let arg, ret = split_typ_list t in
        { v=TypeDecl (f, [], c, arg, ret); beg_pos=$startpos; end_pos=$endpos; } }

| f=LINDENT "::" "forall" l=LINDENT+ "." c=class_list t=separated_nonempty_list("->", typ)
    { let arg, ret = split_typ_list t in
        { v=TypeDecl (f, l, c, arg, ret); beg_pos=$startpos; end_pos=$endpos; } }


class_list:
| v=ntype "=>"                  { [v] }
| l=class_list v=ntype "=>"     { v::l }


instance:
| r=ntype
    { (r, []) }

| a=ntype "=>" r=ntype
    { (r, [a]) }

| "(" l=separated_nonempty_list(",", ntype) ")" "=>" r=ntype
    { (r, l) }


ntype: cstr=UINDENT arg=atype*
    { { v=AstTData (cstr, arg); beg_pos=$startpos; end_pos=$endpos; } }

atype:
| c=UINDENT         { { v=AstTData (c, []); beg_pos=$startpos; end_pos=$endpos; } }
| t=non_const_type  { t }

typ:
| t=non_const_type  { t }
| t=ntype           { t }

non_const_type:
| v=LINDENT         { { v=AstTVar v; beg_pos=$startpos; end_pos=$endpos; } }
| "(" t=typ ")"     { t }


pattern:
| p=patarg            { p }
| c=UINDENT arg=patarg+
                      { { v=PatConstructor (c, arg); beg_pos=$startpos; end_pos=$endpos } }


patarg:
| c=constant          { { v=PatConst c; beg_pos=$startpos; end_pos=$endpos } }
| v=LINDENT           { { v=PatVar v; beg_pos=$startpos; end_pos=$endpos } }
// An Uindent can only be a "zeroary" Constructor
// because we have no record in MiniPureScript
| c=UINDENT           { { v=PatConstructor (c, []); beg_pos=$startpos; end_pos=$endpos } }
| "(" p=pattern ")"   { p }


constant:
| "true"      { { v=True; beg_pos=$startpos; end_pos=$endpos } }
| "false"     { { v=False; beg_pos=$startpos; end_pos=$endpos } }
| i=INT_CST   { { v=Int i; beg_pos=$startpos; end_pos=$endpos } }
| s=STR_CST   { { v=Str s; beg_pos=$startpos; end_pos=$endpos } }


atom:
| c=constant                { { v=ExprConst c; beg_pos=$startpos; end_pos=$endpos } }
| v=LINDENT                 { { v=ExprVar v; beg_pos=$startpos; end_pos=$endpos } }
// An Uindent can only be a "zeroary" Constructor
// because we have no record in MiniPureScript
| c=UINDENT                 { { v=AppConst (c, []); beg_pos=$startpos; end_pos=$endpos } }
| "(" e=expr ")"            { e }
| "(" e=expr "::" t=typ ")" { { v=WithType (e, t); beg_pos=$startpos; end_pos=$endpos } }


expr:
| a=atom
    { a }

| "-" e=expr
    { { v=Neg e; beg_pos=$startpos; end_pos=$endpos } } %prec U_MINUS

| l=expr op=binop r=expr
    { { v=BinOp (l, op, r); beg_pos=$startpos; end_pos=$endpos } }

| f=LINDENT arg=atom+
    { { v=AppFun (f, arg); beg_pos=$startpos; end_pos=$endpos } }

| f=UINDENT arg=atom+
    { { v=AppConst (f, arg); beg_pos=$startpos; end_pos=$endpos } }

| "if" c=expr "then" tb=expr "else" tf=expr
    { { v=If (c, tb, tf); beg_pos=$startpos; end_pos=$endpos } }

| "do" "{" l=separated_nonempty_list(";", expr) "}"
    { { v=Block l; beg_pos=$startpos; end_pos=$endpos } }

| "let" "{" bl=separated_nonempty_list(";", binding) "}" "in" e=expr
    { { v=Let (bl, e); beg_pos=$startpos; end_pos=$endpos } }

| "case" e=expr "of" "{" bl=separated_nonempty_list(";", branch) "}"
    { { v=Case (e, bl); beg_pos=$startpos; end_pos=$endpos } }


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
