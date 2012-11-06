%{
open Error
open Types
%}

%token <string> IDENT
%token <int> INT
%token <Types.operator> OP
%token PLUS MINUS
%token AND OR NOT
%token LPAREN RPAREN
%token SEMICOLON
%token EOF

%nonassoc SEMICOLON
%left AND OR
%right NOT
%left PLUS MINUS

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
    | NOT formulae              { negateFormula $2 }
;

formula:
    | expr OP expr  { ($2, $1 -- $3) }
;

expr:
    | term              { $1 }
    | expr PLUS term    { $1 ++ $3 }
    | expr MINUS term   { $1 -- $3 }
;

term:
    | num       { M.add "" $1 M.empty }
    | num IDENT { M.add $2 $1 M.empty }
    | IDENT     { M.add $1 1 M.empty }
;

num:
    | INT       { $1 }
    | PLUS INT  { $2 }
    | MINUS INT { -($2) }
;
