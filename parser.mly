%{
open Error
open Types
%}

%token <string> IDENT
%token <int> INT
%token <Types.operator> OP
%token PLUS MINUS
%token AND OR
%token LPAREN RPAREN
%token SEMICOLON
%token EOF

%start inputUnit
%type <Types.expr Types.formula list> inputUnit

%%

inputUnit:
    /* TODO: Support multiple formulae group */
    | formulae SEMICOLON formulae EOF { [$1;$3] }
;

formulae:
    | formula                   { Expr($1) }
    | LPAREN formulae RPAREN    { $2 }
    | formulae AND formulae     { combineFormulae true $1 $3 }
    | formulae OR formulae      { combineFormulae false $1 $3 }
;

formula:
    | expr OP expr  { normalizeExpr ($2, $1, $3) }
;

expr:
    | term              { [$1] }
    | expr PLUS term    { $1 @ [$3] }
    | expr MINUS term   { let (a, b) = $3 in $1 @ [ (-a, b) ] }
;

term:
    | num       { ($1, "") }
    | num IDENT { ($1, $2) }
    | IDENT     { (1, $1) }
;

num:
    | INT       { $1 }
    | PLUS INT  { $2 }
    | MINUS INT { -($2) }
;
