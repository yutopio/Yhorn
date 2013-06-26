open Buffer
open ListEx
open MapEx
open Util

module M = Map.Make(Id)
module S = Set.Make(Id)

module Integer = struct
  type t = int
  let compare = compare
  let hash x = x
  let equal = (=)
end

module MI = Map.Make(Integer)

module MyIntList = struct
  type t = int list
  let compare = compare
end

module MIL = Map.Make(MyIntList)

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

let operator_of_string = function
    | "=" -> EQ
    | "<>" -> NEQ
    | "<" -> LT
    | "<=" -> LTE
    | ">" -> GT
    | ">=" -> GTE

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
let (~--) = M.map (~-)

type expr = operator * coef
type pvar = Id.t * Id.t list

let printTerm coef =
  let buf = create 1 in
  let first = ref true in
  M.iter (fun v c ->
    if v = Id.const || c = 0 then () else (
      if c > 0 && not !first then add_char buf '+'
      else if c = -1 then add_char buf '-';
      first := false;
      if (abs c) <> 1 then add_string buf (string_of_int c);
      add_string buf (Id.print v))) coef;
  let c = M.findDefault 0 Id.const coef in
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
      | LT -> LTE, (M.addDefault 0 (+) Id.const 1 coef)
      | GT -> LTE, (M.addDefault 0 (+) Id.const 1 (~-- coef))
      | GTE -> LTE, (~-- coef)
      | _ -> op, coef in
  let coef = M.filter (fun _ v -> v <> 0) coef in
  if M.cardinal coef = 1 && M.mem Id.const coef then
    match op with
      | EQ -> NEQ, M.empty
      | NEQ -> EQ, M.empty
      | LTE ->
        if M.find Id.const coef <= 0 then EQ, M.empty
        else LTE, M.add Id.const 1 M.empty
  else
    op, coef

let negateExpr (op, coef) = (negateOp op, coef)

let renameVar m k =
  if k = Id.const then Id.const
  else (
    if not (M.mem k !m) then
      m := M.add k (Id.create ()) !m;
    M.find k !m)
let renameExpr m (op, coef) = op,
  M.fold (renameVar m |- M.addDefault 0 (+)) coef M.empty
let renameList m = List.map (renameVar m)

let printPvar (name, params) =
  (Id.print name) ^ "(" ^
    String.concat "," (List.map Id.print params) ^ ")"

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

let rec normalizeOperator = function
  | And x -> List.reduce (&&&) (List.map normalizeOperator x)
  | Or x -> List.reduce (|||) (List.map normalizeOperator x)
  | Expr (NEQ, coef) -> Or (
    List.map (fun x -> Expr (normalizeExpr (x, coef))) [LT;GT])
  | Expr (EQ, coef) -> And (
    List.map (fun x -> Expr (normalizeExpr (x, coef))) [LTE;GTE])
  | Expr e -> Expr e

let rec countFormula = function
    | And x
    | Or x -> List.fold_left (+) 0 (List.map countFormula x)
    | Expr _ -> 1

let rec fvs = function
  | And x
  | Or x -> List.fold_left (fun s -> fvs |- S.union s) S.empty x
  | Expr (_, coef) ->
    (* TODO: Rewrite M.keys to return a set. *)
    M.fold (fun k _ -> S.add k) coef S.empty |>
    S.remove Id.const

type hornTerm =
    | LinearExpr of expr formula
    | PredVar of pvar
type horn = hornTerm formula * hornTerm

let printHornTerm = function
    | LinearExpr e -> printFormula printExpr e
    | PredVar p -> printPvar p

let renameHornTerm m = function
    | LinearExpr e -> LinearExpr (mapFormula (renameExpr m) e)
    | PredVar (p, param) -> PredVar (p, renameList m param)

let printHorn (lh, rh) =
  printFormula printHornTerm lh ^ " -> " ^ printHornTerm rh ^ "."

(** Normal form of element *)
type 'a nf = 'a list list

let convertToNF cnf formulae =
    let rec internal formulae ret =
        match formulae with
        | [] -> List.rev ret
        | x :: l ->
            let ret = match x with
                | Expr x -> [ x ] :: ret
                | And x | Or x -> (List.direct_product (internal x [])) @ ret in
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
type pcoef = coef M.t
let (+++) = coefOp (++) M.empty

let renamePexpr m (op, coef) = op,
  M.fold (renameVar m |- M.addDefault M.empty (++)) coef M.empty
let printPexpr coef =
  let buf = create 1 in
  let first = ref true in
  M.iter (fun v coef ->
    let term = printTerm coef in
    if v = Id.const || term = "0" then () else (
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
    add_string buf (Id.print v))) coef;
  if !first then add_string buf "0";
  add_string buf " <= ";
  add_string buf (
    if M.mem Id.const coef then
      printTerm (~-- (M.find Id.const coef))
    else "0");
  contents buf


(* TODO: Should have been moved to constr.ml *)
type constr = expr formula
type constrSet = Id.t list * Puf.t * constr MI.t

type hornSolSpace = horn list * ((Id.t list * pcoef nf) M.t * constrSet)
type hornSol = (Id.t list * expr formula) M.t

let printHornSol x =
  let buf = create 1 in
  M.iter (fun k (params, x) ->
    Id.print k ^ "(" ^ (String.concat "," (List.map Id.print params)) ^ ") : "
      ^ (printFormula printExpr x) ^ "\n" |>
    add_string buf) x;
  contents buf

(* Ocamlgraph related types *)

module MyVertex = struct
  type t = hornTerm
  let compare = compare
  let hash _ = 0 (* TODO: *)
  let equal = (=)
end

module MyEdge = struct
  type t = Id.t M.t option

  let compare x y = match x, y with
    | None, None -> 0
    | _, None -> -1
    | None, _ -> 1
    | Some x, Some y -> M.compare compare x y

  let default = None
end

module G = Graph.Persistent.Digraph.AbstractLabeled(MyVertex)(MyEdge)
module SV = Set.Make(G.V)
module Traverser = Graph.Traverse.Dfs(G)
module Operator = Graph.Oper.P(G)

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

  let highlight_vertices = ref SV.empty
  let vertex_attributes v =
    if SV.mem v !highlight_vertices then
      [`Style `Filled ; `Fillcolor 0; `Fontcolor 0xffffff]
    else []

  let edge_label e =
    match E.label e with
      | None -> ""
      | Some x ->
        let r = M.fold (fun x y l ->
          (Id.print x ^ "=" ^ Id.print y) :: l) x [] in
        String.concat ", " r

  let edge_attributes e =
    match E.label e with
      | None -> [`Style `Dashed]
      | Some _ -> [`Label (edge_label e)]
end

module Dot = Graph.Graphviz.Dot(Display)

let uname =
  let (i, o) as p = Unix.open_process "uname" in
  let ret = input_line i in
  ignore(Unix.close_process p);
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
  ) else (
    let pdf = Filename.temp_file "graph" ".pdf" in
    ignore (Sys.command ("ps2pdf " ^ ps ^ " " ^ pdf));
    ignore (Sys.command ("open " ^ pdf));
    ignore (read_line ())
  );
  Sys.remove dot

let display_with_gv x =
  if !Flags.enable_gv then display Dot.output_graph x else ()
