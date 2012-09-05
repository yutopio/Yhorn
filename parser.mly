%{
open Error
open Types

let combineFormulae opAnd x y =
    match (opAnd, x, y) with
    | (true, And x, And y) -> And(y @ x)
    | (true, And x, _) -> And(y :: x)
    | (true, _, And y) -> And(y @ [ x ])
    | (true, _, _) -> And [ y ; x ]
    | (_, Or x, Or y) -> Or(y @ x)
    | (_, Or x, _) -> Or(y :: x)
    | (_, _, Or y) -> Or(y @ [ x ])
    | _ -> Or [ y ; x ]
%}

%token <string> IDENT
%token <float> FLOAT
%token <int> OP
%token PLUS MINUS
%token AND OR
%token LPAREN RPAREN
%token SEMICOLON
%token EOF

%start inputUnit
%type <Types.formula list> inputUnit

%%

inputUnit:
    | formulae SEMICOLON formulae EOF { [$1;$3] }
;

formulae:
    | formula                   { Expr($1) }
    | LPAREN formulae RPAREN    { $2 }
    | formulae AND formulae     { combineFormulae true $1 $3 }
    | formulae OR formulae      { combineFormulae false $1 $3 }
;

formula:
    | expr OP expr  { ($2, $1, $3) }
;

expr:
    | term              { [$1] }
    | expr PLUS term    { $1 @ [$3] }
    | expr MINUS term   { let (a, b) = $3 in $1 @ [ (-.a, b) ] }
;

term:
    | num       { ($1, "") }
    | num IDENT { ($1, $2) }
    | IDENT     { (1., $1) }
;

num:
    | FLOAT         { $1 }
    | PLUS FLOAT    { $2 }
    | MINUS FLOAT   { -.($2) }
;