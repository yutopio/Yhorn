open Buffer
open Util

module MyString = struct
  type t = string
  let compare = compare
end

module M = MapEx.Make(MyString)
module S = Set.Make(MyString)

module MyInt = struct
  type t = int
  let compare = compare
end

module MI = MapEx.Make(MyInt)

module MyIntList = struct
  type t = int list
  let compare = compare
end

module MIL = MapEx.Make(MyIntList)

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
    | EQ -> "="
    | NEQ -> "<>"
    | LT -> "<"
    | LTE -> "<="
    | GT -> ">"
    | GTE -> ">="

type coef = int M.t

let coefOp op d = M.fold (M.addDefault d op)
let (++) = coefOp (+) 0
let (--) x y = coefOp (-) 0 y x (* Note that the operands need to be reversed. *)
let (~--) = M.map (fun v -> -v)

type expr = operator * coef
type pvar = string * string list

let printTerm coef =
  let buf = create 1 in
  let first = ref true in
  M.iter (fun v c ->
    if v = "" || c = 0 then () else (
      if c > 0 && not !first then add_char buf '+'
      else if c = -1 then add_char buf '-';
      first := false;
      if (abs c) <> 1 then add_string buf (string_of_int c);
      add_string buf v)) coef;
  let c = M.findDefault 0 "" coef in
  if not !first && c > 0 then add_char buf '+';
  if !first || c <> 0 then add_string buf (string_of_int c);
  contents buf

let printExpr (op, coef) =
  let buf = create 1 in
  add_string buf (printTerm coef);
  add_string buf (string_of_operator op);
  add_char buf '0';
  contents buf

(** Flips greater-than operators (>, >=) to less-than operators (<, <=) and
    replaces strict inequality (<, >) with not strict ones (<=, >=) by adding 1
    on constant term. Any variables with 0-weight are eliminated. Returns the
    operator and the coefficient mapping. *)
let normalizeExpr (op, coef) =
  let op, coef =
    match op with
      | LT -> LTE, (M.addDefault 0 (+) "" 1 coef)
      | GT -> LTE, (M.addDefault 0 (+) "" 1 (~-- coef))
      | GTE -> LTE, (~-- coef)
      | _ -> op, coef in
  let coef = M.filter (fun _ v -> v <> 0) coef in
  if M.cardinal coef = 1 && M.mem "" coef then
    match op with
      | EQ -> NEQ, M.empty
      | NEQ -> EQ, M.empty
      | LTE ->
        if M.find "" coef <= 0 then EQ, M.empty
        else LTE, M.add "" 1 M.empty
  else
    op, coef

let negateExpr (op, coef) = (negateOp op, coef)

let rec renameVar m k =
  assert (k <> "");
  if not (M.mem k !m) then
    m := M.add k (new_name ()) !m;
  M.find k !m
and renameExpr m (op, coef) = op,
  M.fold (fun k ->
    let k = if k = "" then "" else renameVar m k in
    M.addDefault 0 (+) k) coef M.empty
and renameList m = List.map (renameVar m)

let printPvar (name, params) =
    name ^ "(" ^ String.concat "," params ^ ")"

type 'a formula =
    | Expr of 'a
    | And of 'a formula list
    | Or of 'a formula list

let rec printFormula eltPrinter x =
    let ret = match x with
    | Expr x -> `A x
    | And x -> `B(x, " & ")
    | Or x -> `B(x, " | ") in

    match ret with
    | `A x -> eltPrinter x
    | `B(x, y) -> String.concat y (List.map (
        fun x -> "(" ^ (printFormula eltPrinter x) ^ ")") x)

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
let (&&&) x = combineFormulae true x
let (|||) x = combineFormulae false x

let rec mapFormula f = function
    | And x -> And (List.map (mapFormula f) x)
    | Or x -> Or (List.map (mapFormula f) x)
    | Expr e -> Expr (f e)

let rec (!!!) = function
    | And x -> Or (List.map (!!!) x)
    | Or x -> And (List.map (!!!) x)
    | Expr e -> Expr (negateExpr e)

let (==>) x y = (!!! x) ||| y
let (<=>) x y = (x ==> y) &&& (y ==> x)

let rec splitNegation = function
    | And x -> reduce (&&&) (List.map splitNegation x)
    | Or x -> reduce (|||) (List.map splitNegation x)
    | Expr (NEQ, coef) -> Or (
      List.map (fun x -> Expr (normalizeExpr (x, coef))) [LT;GT])
    | Expr e -> Expr e

let rec countFormula = function
    | And x
    | Or x -> List.fold_left (+) 0 (List.map countFormula x)
    | Expr _ -> 1

type hornTerm =
    | LinearExpr of expr formula
    | PredVar of pvar
type horn = hornTerm list * hornTerm

let printHornTerm = function
    | LinearExpr e -> printFormula printExpr e
    | PredVar p -> printPvar p

let renameHornTerm m = function
    | LinearExpr e -> LinearExpr (mapFormula (renameExpr m) e)
    | PredVar (p, param) -> PredVar (p, renameList m param)

let printHorn (lh, rh) =
  let preds, la = List.partition (function PredVar _ -> true | _ -> false) lh in
  String.concat " & " (List.map printHornTerm (preds @ la)) ^ " -> " ^
    printHornTerm rh ^ "."

(** Normal form of element *)
type 'a nf = 'a list list

let convertToNF cnf formulae =
    let rec internal formulae ret =
        match formulae with
        | [] -> List.rev ret
        | x :: l ->
            let ret = match x with
                | Expr x -> [ x ] :: ret
                | And x | Or x -> (directProduct (internal x [])) @ ret in
            internal l ret in
    match cnf, formulae with
    | true, And x
    | false, Or x -> internal x []
    | _ -> internal [ formulae ] []

let convertToFormula cnf nf =
  match List.map (fun x ->
    match List.map (fun x -> Expr x) x with
      | [] -> assert false
      | [x] -> x
      | x -> if cnf then Or x else And x) nf with
    | [] -> assert false
    | [x] -> x
    | x -> if cnf then And x else Or x

(** Solution space of interpolation *)
type pexpr = operator M.t * coef M.t
let (+++) = coefOp (++) M.empty

let renamePexpr m (op, coef) = op,
  M.fold (fun k ->
    let k = if k = "" then "" else renameVar m k in
    M.addDefault M.empty (++) k) coef M.empty
let printPexpr (_, coef) =
  let buf = create 1 in
  let first = ref true in
  M.iter (fun v coef ->
    let term = printTerm coef in
    if v = "" || term = "0" then () else (
    if not !first then add_char buf '+';
    first := false;
    if (String.contains term '+') || (String.contains term '-') then (
      add_char buf '(';
      add_string buf term;
      add_char buf ')'
    ) else (
      add_string buf term;
      add_char buf '*'
    );
    add_string buf v)) coef;
  if !first then add_string buf "0";
  add_string buf " ? ";
  add_string buf (if M.mem "" coef then printTerm (M.find "" coef) else "0");
  contents buf

type constr = expr formula
type space = pexpr * constr

type constrSet = int list * Puf.t * constr MI.t
type hornSolSpace = horn list * ((string list * pexpr nf) M.t * constrSet)
type hornSol = (string list * expr formula) M.t

(* Ocamlgraph related types *)

module MyVertex = struct
  type t = hornTerm
  let compare = compare
  let hash _ = 0 (* TODO: *)
  let equal = (=)
end

type hornTermId = La of int | Pid of int
module MyVertex' = struct
  type t = hornTermId
  let compare = compare
  let hash _ = 0 (* TODO: *)
  let equal = (=)
end

module MyEdge = struct
  type t = (string * string) list option

  let compare x y = match x, y with
    | None, None -> 0
    | _, None -> -1
    | None, _ -> 1
    | Some x, Some y ->
      match (List.length x) - (List.length y) with
        | 0 ->
          let [x;y] = List.map (List.sort comparePair) [x;y] in
          listFold2 (fun a x y -> match a with
            | 0 -> comparePair x y
            | _ -> a) 0 x y
        | ret -> ret

  let default = None
end

module G = Graph.Persistent.Digraph.AbstractLabeled(MyVertex)(MyEdge)
module G' = Graph.Persistent.Digraph.AbstractLabeled(MyVertex')(MyEdge)
module Traverser = Graph.Traverse.Dfs(G)
module Operator = Graph.Oper.P(G)
module Sorter = Graph.Topological.Make(G')

module DisplayAttrib = struct
  let graph_attributes _ = []
  let default_vertex_attributes _ = [`Fontname "Courier"; `Shape `Box]
  let vertex_attributes _ = []
  let default_edge_attributes _ = [`Fontname "Courier"]

  let get_subgraph _ = None
end

module Display = struct
  include G
  include DisplayAttrib
  let vertex_name v = "\"" ^ (string_of_int (V.hash v)) ^ ":" ^
                             (printHornTerm (V.label v)) ^ "\""
  let edge_attributes e =
    match E.label e with
      | None -> []
      | Some x ->  [`Label (String.concat ", "
                           (List.map (fun (x, y) -> x ^ "=" ^ y) x))]
end

module Display' = struct
  include G'
  include DisplayAttrib
  let vertex_name v = "\"" ^
    (match V.label v with
      | La x -> "La " ^ (string_of_int x)
      | Pid x -> "Pid " ^ (string_of_int x)) ^ "\""
  let edge_attributes e =
    match E.label e with
      | None -> []
      | Some x ->  [`Label (String.concat ", "
                           (List.map (fun (x, y) -> x ^ "=" ^ y) x))]
end

module Dot = Graph.Graphviz.Dot(Display)
module Dot' = Graph.Graphviz.Dot(Display')

let uname =
  let (i, o) as p = Unix.open_process "uname" in
  let ret = input_line i in
  Unix.close_process p;
  ret

let display output_graph g =
  let dot = Filename.temp_file "graph" ".dot" in
  let ps = Filename.temp_file "graph" ".ps" in
  let oc = open_out dot in
  output_graph oc g;
  close_out oc;
  ignore (Sys.command ("dot -Tps " ^ dot ^ " > " ^ ps));
  if uname <> "Darwin" then (
    ignore (Sys.command ("gv " ^ ps ^ " 2>/dev/null"));
    Sys.remove ps
  ) else
    ignore (Sys.command ("open " ^ ps));
  Sys.remove dot

let display_with_gv _ = ()
let display_with_gv' _ = ()

(* DEBUG: *)
let display_with_gv = display Dot.output_graph
let display_with_gv' = display Dot'.output_graph
