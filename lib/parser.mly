
/* Analyseur syntaxique pour Mini-Python */

%{

%}

%token EOF

%start file

%type <int option> file

%%
file:
EOF { None }