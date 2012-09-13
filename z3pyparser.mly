%{
open Types
%}

%token <int> INT
%token LBR RBR EQ COMMA
%token EOF

%start inputUnit
%type <int Types.MI.t> inputUnit

%%

inputUnit:
    | LBR RBR EOF               { MI.empty }
    | LBR assignments RBR EOF   { $2 }
;

assignments:
    | assignment                    { $1 MI.empty }
    | assignments COMMA assignment  { $3 $1 }
;

assignment:
    | INT EQ INT    { MI.add $1 $3 }
;
