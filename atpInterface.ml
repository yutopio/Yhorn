open Util
open Types

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
      else reduce (fun a b -> Atp_batch.Fn("+", [a; b])) l) [c1; ~--c2] in

    (* Connect two terms with a relation symbol. *)
    let r = string_of_operator op in
    if op = NEQ then Atp_batch.Not(Atp_batch.Atom(Atp_batch.R("=", terms)))
    else Atp_batch.Atom(Atp_batch.R(r, terms))

let rec of_formula = function
  | Expr e -> of_expr e
  | And l -> reduce Atp_batch.mk_and (List.map of_formula l)
  | Or l -> reduce Atp_batch.mk_or (List.map of_formula l)

let rec term_of = function
  | Atp_batch.Var(id) -> M.add (Id.deserialize id) 1 M.empty
  | Atp_batch.Fn("+", [t1; t2]) -> (term_of t1) ++ (term_of t2)
  | Atp_batch.Fn("-", [t1; t2]) -> (term_of t1) -- (term_of t2)
  | Atp_batch.Fn("-", [t]) -> ~-- (term_of t)
  | Atp_batch.Fn("*", ts) ->
    let ts = List.map term_of ts in
    assert (List.for_all (M.cardinal |- (=) 1) ts);
    let ts = reduce (@) (List.map M.bindings ts) in
    let [v] = (List.map fst ts) |> List.filter ((<>) Id.const) in
    let c = (List.map snd ts) |> reduce ( * ) in
    M.add v c M.empty
  | Atp_batch.Fn(s, []) -> M.add Id.const (int_of_string s) M.empty
  | Atp_batch.Fn(s, ts) -> assert false

let rec formula_of p =
  match p with
  | Atp_batch.True -> Expr (EQ, M.empty)
  | Atp_batch.False -> Expr (NEQ, M.empty)
  | Atp_batch.Not p -> (!!!) (formula_of p)
  | Atp_batch.And(p1, p2) -> (formula_of p1) &&& (formula_of p2)
  | Atp_batch.Or(p1, p2) -> (formula_of p1) ||| (formula_of p2)
  | Atp_batch.Atom(Atp_batch.R(r, ts)) ->
    let [t1; t2] = List.map term_of ts in
    Expr (operator_of_string r, t1 -- t2)
  | _ -> (
    Atp_batch.print_formula Atp_batch.print_atom p;
    print_newline ();
    assert false)

let integer_qelim vars la =
  let vars = S.diff (fvs la) vars in
  of_formula la |>
  S.fold (fun id ast -> Atp_batch.Exists(Id.serialize id, ast)) vars |>
  Atp_batch.integer_qelim |>
  Atp_batch.simplify |>
  formula_of
