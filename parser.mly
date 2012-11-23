%{
open Error
open Types

let pVarAdd (x, y) = M.add x y
%}

%token <string> VAR
%token <string> PRED
%token <int> INT
%token <Types.operator> OP
%token PLUS MINUS
%token AND OR NOT
%token LPAREN RPAREN
%token ARROW DOT COMMA
%token EOF

%nonassoc ARROW
%left CAND
%left AND OR
%right NOT
%left PLUS MINUS

%start inputUnit
%type <Types.horn list> inputUnit

%%

inputUnit:
    | EOF                   { [] }
    | hornClause inputUnit  { $1::$2 }
;

hornClause:
    | clause ARROW pred DOT     { $1, (PredVar $3) }
    | clause ARROW exprs DOT    { $1, (LinearExpr $3) }
;

clause:
    | exprs                         { (M.empty, Some $1) }
    | pred                          { (pVarAdd $1 M.empty, None) }
    | clause AND exprs %prec CAND   { let (a, b) = $1 in a, Some(
                                      match b with
                                      | Some e -> e &&& $3
                                      | None -> $3) }
    | clause AND pred               { let (a, b) = $1 in pVarAdd $3 a, b  }
;

pred:
    | PRED                          { ($1, []) }
    | PRED LPAREN RPAREN            { ($1, []) }
    | PRED LPAREN predParam RPAREN  { ($1, $3) }
;

predParam:
    | VAR                   { [$1] }
    | VAR COMMA predParam   { $1::$3 }
;

exprs:
    | expr                  { Expr $1 }
    | LPAREN exprs RPAREN   { $2 }
    | exprs AND exprs       { $1 &&& $3 }
    | exprs OR exprs        { $1 ||| $3 }
    | NOT exprs             { !!! $2 }
;

expr:
    | terms OP terms    { ($2, $1 -- $3) }
;

terms:
    | term              { $1 }
    | terms PLUS term   { $1 ++ $3 }
    | terms MINUS term  { $1 -- $3 }
;

term:
    | num       { M.add "" $1 M.empty }
    | num VAR   { M.add $2 $1 M.empty }
    | VAR       { M.add $1 1 M.empty }
;

num:
    | INT       { $1 }
    | PLUS INT  { $2 }
    | MINUS INT { -($2) }
;
