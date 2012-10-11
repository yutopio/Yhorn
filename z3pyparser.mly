%{
open Types
%}

%token <int> INT
%token <string> STR
%token LBR RBR EQ COMMA
%token EOF

%start inputUnit
%type <int Types.M.t> inputUnit

%%

inputUnit:
    | LBR RBR EOF               { M.empty }
    | LBR assignments RBR EOF   { $2 }
;

assignments:
    | assignment                    { $1 M.empty }
    | assignments COMMA assignment  { $3 $1 }
;

assignment:
    | STR EQ INT    { M.add $1 $3 }
;
