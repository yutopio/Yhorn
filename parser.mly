%{
open Error
open Types
%}

%token <string> VAR
%token <string> PRED
%token <int> INT
%token <Types.operator> OP
%token PLUS MINUS
%token AND OR NOT
%token LPAREN RPAREN
%token SEMICOLON DBLSEMICOLON COMMA
%token EOF

%nonassoc SEMICOLON
%left CAND
%left AND OR
%right NOT
%left PLUS MINUS

%start inputUnit
%type <Types.horn list> inputUnit

%%

inputUnit:
    | hornClause EOF                    { [$1] }
    | hornClause DBLSEMICOLON inputUnit { $1::$3 }
;

hornClause:
    | clause SEMICOLON pred     { $1, (PredVar $3) }
    | clause SEMICOLON exprs    { $1, (LinearExpr $3) }
;

clause:
    | hornTerm                          { [$1] }
    | hornTerm AND clause %prec CAND    { $1::$3 }
;

hornTerm:
    | exprs                 { LinearExpr $1 }
    | pred                  { PredVar $1 }
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
