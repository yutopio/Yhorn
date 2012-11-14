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
%token SEMICOLON DBLSEMICOLON
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
    | clause SEMICOLON PRED     { $1, (PredVar $3) }
    | clause SEMICOLON exprs    { $1, (LinearExpr $3) }
;

clause:
    | exprs                         { (SP.empty, Some $1) }
    | PRED                          { (SP.add $1 SP.empty, None) }
    | clause AND exprs %prec CAND   { let (a, b) = $1 in a, Some(
                                      match b with
                                      | Some e -> e &&& $3
                                      | None -> $3) }
    | clause AND PRED               { let (a, b) = $1 in SP.add $3 a, b  }
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
