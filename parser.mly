%{
open Error
open Expr
open Formula
open MTypes
open Types
%}

%token <Id.t> VAR
%token <Id.t> PRED
%token <int> INT
%token <Expr.operator> OP
%token PLUS MINUS
%token AND OR NOT
%token LPAREN RPAREN
%token ARROW DOT COMMA
%token EOF

%nonassoc ARROW
%left AND OR
%right NOT
%left PLUS MINUS

%start inputUnit
%type <Types.horn list> inputUnit

%%

inputUnit:
    | hornClauses EOF { $1 }
;

hornClauses:
    | hornClause                { [$1] }
    | hornClause hornClauses    { $1::$2 }
;

hornClause:
    | hterms ARROW pred  DOT    { $1, (PredVar $3) }
    | hterms ARROW exprs DOT    { $1, (LinearExpr $3) }
;

hterms:
    | exprs                 { Term (LinearExpr $1) }
    | pred                  { Term (PredVar $1) }
    | LPAREN hterms RPAREN  { $2 }
    | hterms AND hterms     { And [$1;$3] }
    | hterms OR  hterms     { Or [$1;$3] }
;

pred:
    | PRED                          { ($1, []) }
    | PRED LPAREN           RPAREN  { ($1, []) }
    | PRED LPAREN predParam RPAREN  { ($1, $3) }
;

predParam:
    | VAR                   { [$1] }
    | VAR COMMA predParam   { $1::$3 }
;

exprs:
    | expr                  { Term $1 }
    | LPAREN exprs RPAREN   { $2 }
    | exprs AND exprs       { $1 &&& $3 }
    | exprs OR  exprs       { $1 ||| $3 }
    | NOT exprs             { !!! $2 }
;

expr:
    | terms OP    terms { ($2, $1 -- $3) }
;

terms:
    |             term  { $1 }
    |       PLUS  term  { $2 }
    |       MINUS term  { M.empty -- $2 }
    | terms PLUS  term  { $1 ++ $3 }
    | terms MINUS term  { $1 -- $3 }
;

term:
    | INT       { M.add Id.const $1 M.empty }
    | INT VAR   { M.add $2 $1 M.empty }
    |     VAR   { M.add $1 1 M.empty }
;
