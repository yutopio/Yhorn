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

(* This procedure sums up all terms according to the variable and move to the
   left-side of the expression. It flips greater-than operators (>, >=) to
   less-than operators (<, <=) and replaces strict inequality (<, >) with not
   strict ones (<=, >=) by doing +/- 1 on constant term. Returns the operator
   and the mapping from a variable to its coefficient. The constant term has the
   empty string as a key. *)
let normalizeExpr (op, t1, t2) =
    let addCoef sign coefs (coef, key) =
        M.add key (sign * coef +
            (if M.mem key coefs then M.find key coefs else 0)) coefs in
    let t2, sign, op =
        match op with
        | LT -> (-1, "") :: t2, 1, LTE
        | GT -> (1, "") :: t2, -1, LTE
        | GTE -> t2, -1, LTE
        | _ -> t2, 1, op in
    let coefs = M.add "" 0 M.empty in
    let coefs = List.fold_left (addCoef sign) coefs t1 in
    let coefs = List.fold_left (addCoef (-sign)) coefs t2 in
    let coefs = M.fold (fun k v coefs ->
        if k <> "" && v = 0 then M.remove k coefs else coefs) coefs coefs in
    op, coefs
%}

%token <string> IDENT
%token <int> INT
%token <Types.operator> OP
%token PLUS MINUS
%token AND OR
%token LPAREN RPAREN
%token SEMICOLON
%token EOF

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
;

formula:
    | expr OP expr  { normalizeExpr ($2, $1, $3) }
;

expr:
    | term              { [$1] }
    | expr PLUS term    { $1 @ [$3] }
    | expr MINUS term   { let (a, b) = $3 in $1 @ [ (-a, b) ] }
;

term:
    | num       { ($1, "") }
    | num IDENT { ($1, $2) }
    | IDENT     { (1, $1) }
;

num:
    | INT       { $1 }
    | PLUS INT  { $2 }
    | MINUS INT { -($2) }
;
