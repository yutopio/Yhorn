%{
open Types
%}

%token <int> INT
%token <string> STR
%token LBR RBR EQ COMMA
%token NO_SOL
%token EOI

%start inputUnit
%type <int Types.M.t option> inputUnit

%%

inputUnit:
    | NO_SOL EOI                { None }
    | LBR RBR EOI               { Some M.empty }
    | LBR assignments RBR EOI   { Some $2 }
;

assignments:
    | assignment                    { $1 M.empty }
    | assignments COMMA assignment  { $3 $1 }
;

assignment:
    | STR EQ INT    { M.add $1 $3 }
;
