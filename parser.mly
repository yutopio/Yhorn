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
%token <int> INT
%token <Types.operator> OP
%token PLUS MINUS ASTERISK
%token LPAREN RPAREN
%token LBRACK RBRACK
%token COMMA
%token INTERPOLATE DOT
%token EOF

%start inputUnit
%type <Types.formula list> inputUnit

%%

inputUnit:
    | INTERPOLATE LPAREN blocks RPAREN DOT EOF  { $3 }
;

blocks:
    | block COMMA blocks    { $1::$3 }
    | block                 { [$1] }
;

block:
    | LBRACK formulae RBRACK    { And($2) }
;

formulae:
    | formula                   { [$1] }
    | formulae COMMA formula    { $1 @ [$3] }
;

formula:
    | expr OP expr          { Expr($2, $1, $3) }
    | LPAREN formula RPAREN { $2 }
;

expr:
    | term                  { [$1] }
    | expr PLUS expr        { $1 @ $3 }
    | expr MINUS term       { let (a, b) = $3 in $1 @ [ (-a, b) ] }
    | LPAREN expr RPAREN    { $2 }
;

term:
    | num                   { ($1, "") }
    | IDENT                 { (1, $1) }
    | term ASTERISK term    { let ((a, b), (c, d)) = ($1, $3) in
                              assert (a = 1 && d = ""); (c, b) }
    | LPAREN term RPAREN    { $2 }
;

num:
    | INT       { $1 }
    | PLUS INT  { $2 }
    | MINUS INT { -($2) }
;
