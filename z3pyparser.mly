%{
open Types
%}

%token <int> INT
%token <string> STR
%token LBR RBR EQ COMMA
%token NO_SOL
%token EOF

%start inputUnit
%type <int Types.M.t option> inputUnit

%%

inputUnit:
    | NO_SOL                    { None }
    | LBR RBR EOF               { Some M.empty }
    | LBR assignments RBR EOF   { Some $2 }
;

assignments:
    | assignment                    { $1 M.empty }
    | assignments COMMA assignment  { $3 $1 }
;

assignment:
    | STR EQ INT    { M.add $1 $3 }
;
