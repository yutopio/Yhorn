open Formula
open Expr
open ListEx
open MTypes
open Types
open Util

let of_expr (op, coef) =
  let coef = M.filter (fun _ -> (<>) 0) coef in
  if M.cardinal coef = 0 then
    (* If no term is given, return the Boolean value. *)
    match op with
    | EQ | LTE | GTE -> Atp_batch.True
    | NEQ | LT | GT -> Atp_batch.False
  else
    let c1, c2 = M.partition (fun _ -> (<) 0) coef in

    (* Build terms. *)
    let int x = Atp_batch.Fn(string_of_int x, []) in
    let terms = List.map (fun x ->
      let l =
        M.fold (fun k v l -> (
          if k = Id.const then int v
          else
            let var = Atp_batch.Var (Id.serialize k) in
            if v = 1 then var
            else Atp_batch.Fn("*", [int v; var])) :: l) x [] in
      if l = [] then int 0
      else List.reduce (fun a b -> Atp_batch.Fn("+", [a; b])) l) [c1; ~--c2] in

    (* Connect two terms with a relation symbol. *)
    let r = string_of_operator op in
    if op = NEQ then Atp_batch.Not(Atp_batch.Atom(Atp_batch.R("=", terms)))
    else Atp_batch.Atom(Atp_batch.R(r, terms))

let rec of_formula = function
  | Term e -> of_expr e
  | And l -> List.reduce Atp_batch.mk_and (List.map of_formula l)
  | Or l -> List.reduce Atp_batch.mk_or (List.map of_formula l)

let rec term_of = function
  | Atp_batch.Var(id) -> M.add (Id.deserialize id) 1 M.empty
  | Atp_batch.Fn("+", [t1; t2]) -> (term_of t1) ++ (term_of t2)
  | Atp_batch.Fn("-", [t1; t2]) -> (term_of t1) -- (term_of t2)
  | Atp_batch.Fn("-", [t]) -> ~-- (term_of t)
  | Atp_batch.Fn("*", ts) ->
    let ts = List.map term_of ts in
    assert (List.for_all (M.cardinal |- (=) 1) ts);
    let ts = List.reduce (@) (List.map M.bindings ts) in
    let [v] = (List.map fst ts) |> List.filter ((<>) Id.const) in
    let c = (List.map snd ts) |> List.reduce ( * ) in
    M.add v c M.empty
  | Atp_batch.Fn(s, []) -> M.add Id.const (int_of_string s) M.empty
  | Atp_batch.Fn(s, ts) -> assert false

let rec formula_of p =
  match p with
  | Atp_batch.True -> Term (EQ, M.empty)
  | Atp_batch.False -> Term (NEQ, M.empty)
  | Atp_batch.Not p -> (!!!) (formula_of p)
  | Atp_batch.And(p1, p2) -> (formula_of p1) &&& (formula_of p2)
  | Atp_batch.Or(p1, p2) -> (formula_of p1) ||| (formula_of p2)
  | Atp_batch.Atom(Atp_batch.R(r, ts)) ->
    let [t1; t2] = List.map term_of ts in
    Term (operator_of_string r, t1 -- t2)
  | _ -> (
    Atp_batch.print_formula Atp_batch.print_atom p;
    print_newline ();
    assert false)

let integer_qelim vars la =
  let (=>) x y = Atp_batch.tautology (Atp_batch.Imp(x, y)) in
  let vars = S.diff (fvs la) vars in
  of_formula la |>
  S.fold (fun id ast -> Atp_batch.Exists(Id.serialize id, ast)) vars |>
  Atp_batch.integer_qelim |>
  Atp_batch.cnf |>
  Atp_batch.conjuncts |>
  List.map (fun ds ->
    try
      let [Term (ox,mx); Term (oy,my)] =
        Atp_batch.disjuncts ds |> List.map formula_of in
      let [mx';my'] = List.map (M.filter (fun k _ -> k <> Id.const)) [mx;my] in
      let [cx;cy] = List.map (M.findDefault 0 Id.const) [mx;my] in
      let (oy, my, cy) =
        if M.compare compare mx' my' <> 0 then
          let oy, my' = flipOp oy, (~--) my' in
          if M.compare compare mx' my' <> 0 then raise Not_found
          else
            let cy = -cy in
            oy, (M.add Id.const cy mx), cy
        else oy, my, cy in
      let ret =
        if cx = cy then
          if ox = oy then ox, mx
          else
            match ox, oy with
            | LT, LTE | LTE, LT | LT, EQ | LTE, EQ | EQ, LT | EQ, LTE -> LTE, mx
            | GT, GTE | GTE, GT | GT, EQ | GTE, EQ | EQ, GT | EQ, GTE -> GTE, mx
            | LT, GT | GT, LT | LT, NEQ | GT, NEQ | NEQ, LT | NEQ, GT -> NEQ, mx
            | _ -> EQ, M.empty
        else
          let ox, mx, oy, my =
            if cx > cy then ox, mx, oy, my
            else oy, my, ox, mx in
          match oy with
          | NEQ | LT | LTE ->
            (match ox with EQ | LT | LTE -> oy, my | _ -> EQ, M.empty)
          | _ -> (match ox with NEQ | GT | GTE -> ox, mx) in
      normalizeExpr ret |> of_expr
    with _ -> ds) |>
  List.reduce Atp_batch.mk_and |>
  formula_of
