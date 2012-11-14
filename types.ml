
open Buffer
open Map
open Set

module MyString = struct
  type t = string
  let compare = compare
end

module M = Map.Make(MyString)

(** [addDefault k v d (+) m] adds value v to the existing record value with key
    k in the given mapping m. Adding is done by (+) function given. If no record
    with key k is present, it will be newly created with the default value d. *)
let addDefault k v d (+) m =
    M.add k ((+) (if M.mem k m then M.find k m else d) v) m

type operator =
    | EQ
    | NEQ
    | LT
    | LTE
    | GT
    | GTE

let negateOp = function
    | EQ -> NEQ
    | NEQ -> EQ
    | LT -> GTE
    | LTE -> GT
    | GT -> LTE
    | GTE -> LT

let string_of_operator = function
    | EQ -> "=="
    | NEQ -> "!="
    | LT -> "<"
    | LTE -> "<="
    | GT -> ">"
    | GTE -> ">="

type coef = int M.t

let coefOp op = M.fold (fun k v -> addDefault k v 0 op)
let (++) = coefOp (+)
let (--) x y = coefOp (-) y x (* Note that the operands need to be reversed. *)
let (~--) = M.map (fun v -> -v)

type expr = operator * coef
type pvar = string

module MyPVar = struct
  type t = pvar
  let compare = compare
end

module MP = Map.Make(MyPVar)
module SP = Set.Make(MyPVar)

let printExpr ?(vars = None) (op, coef) =
    let z3, vars = match vars with
        | Some vars -> true, vars
        | None -> false, ref [] in

    let buf = create 1 in
    let first = ref true in
    M.iter (fun v c ->
        if v = "" || c = 0 then () else (
        if not (List.mem v !vars) then vars := v :: !vars;
        if c > 0 && not !first then add_char buf '+' else if c = -1 then add_char buf '-';
        first := false;
        if (abs c) <> 1 then add_string buf (let c = string_of_int c in if z3 then c ^ "*" else c);
        add_string buf v)) coef;
    if !first then add_string buf "0";
    add_string buf (string_of_operator op);
    add_string buf (if M.mem "" coef then string_of_int (-(M.find "" coef)) else "0");
    contents buf

type 'a formula =
    | Expr of 'a
    | And of 'a formula list
    | Or of 'a formula list

let rec printFormula elementPrinter x =
    let ret = match x with
    | Expr x -> `A x
    | And x -> `B(x, " & ")
    | Or x -> `B(x, " | ") in

    match ret with
    | `A x -> elementPrinter x
    | `B(x, y) -> String.concat y (List.map (
        fun x -> "(" ^ (printFormula elementPrinter x) ^ ")") x)

let combineFormulae opAnd x y =
    match (opAnd, x, y) with
    | (true, And x, And y) -> And (y @ x)
    | (true, And x, _) -> And (y :: x)
    | (true, _, And y) -> And (y @ [ x ])
    | (true, _, _) -> And [ y ; x ]
    | (_, Or x, Or y) -> Or (y @ x)
    | (_, Or x, _) -> Or (y :: x)
    | (_, _, Or y) -> Or (y @ [ x ])
    | _ -> Or [ y ; x ]
let (&&&) : expr formula -> expr formula -> expr formula = combineFormulae true
let (|||) : expr formula -> expr formula -> expr formula = combineFormulae false

(** Flips greater-than operators (>, >=) to less-than operators (<, <=) and
    replaces strict inequality (<, >) with not strict ones (<=, >=) by adding 1
    on constant term. Any variables with 0-weight are eliminated. Returns the
    operator and the coefficient mapping. *)
let normalizeExpr (op, coef) =
    let op, coef =
        match op with
        | LT -> LTE, (addDefault "" 1 0 (+) coef)
        | GT -> LTE, (addDefault "" 1 0 (+) (~-- coef))
        | GTE -> LTE, (~-- coef)
        | _ -> op, coef in
    op, (M.filter (fun k v -> k = "" || v <> 0) coef)

let rec normalizeFormula = function
    | And x -> And (List.map normalizeFormula x)
    | Or x -> Or (List.map normalizeFormula x)
    | Expr e -> Expr (normalizeExpr e)

let rec negateFormula = function
    | And x -> Or (List.map negateFormula x)
    | Or x -> And (List.map negateFormula x)
    | Expr (op, coef) -> Expr (negateOp op, coef)
let (!!!) = negateFormula

let rec countFormula = function
    | And x
    | Or x -> List.fold_left (+) 0 (List.map countFormula x)
    | Expr _ -> 1

type hornTerm =
    | LinearExpr of expr formula
    | PredVar of pvar
type leftHand = SP.t * expr formula option
type rightHand = hornTerm
type horn = leftHand * rightHand

type 'a nf = 'a list list
type space = (operator M.t * coef M.t) * expr formula
