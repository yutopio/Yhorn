open Util
open Types

(* Test wether the constraint is satisfiable or not. *)
let z3test x = not (Z3interface.integer_programming x = None)

let generatePexprUnifyConstr exprs constr =
  assert (List.length exprs >= 2);

  (* Consider all variables are present in both. *)
  let vars = List.fold_left (fun l (_, pcoef) ->
    (M.fold (fun k _ r ->
      if List.exists ((=) k) r then r else k :: r) pcoef l)) [] exprs in

  let (pop1,pcoef1)::en = exprs in
  let i = ref 0 in
  let constrs = List.map (fun (pop, pcoef) ->
    let m = ref M.empty in
    ignore(mapFormula (renameExpr m) constr);
    m := M.map (fun v -> "t" ^ string_of_int (incr i; !i)) !m;

    (* Rename all space information. *)
    let constr = mapFormula (renameExpr m) constr in
    let pop = M.fold (fun k ->
      M.add (if k = "" then "" else renameVar m k)) pop M.empty in
    let pcoef = M.map (fun v -> M.fold (fun k ->
      M.add (if k = "" then "" else renameVar m k)) v M.empty) pcoef in

    (* TODO: We need to consider operator equality between parameterized
       expressions.  pop <---> pop1 *)

    (* Create a condition that restricts all coefficients to be the same. *)
    let eqs = List.map (fun k ->
      let [v1;v2] = List.map (M.findDefault M.empty k) [pcoef1;pcoef] in
      let eqCoef = M.filter (fun _ v -> v <> 0) (v1 -- v2) in
      Expr(EQ, eqCoef)) vars |>
      List.filter (fun x -> x <> Expr(EQ, M.empty)) |>
      distinct in
    match eqs with
      | [] -> Expr (EQ, M.empty) (* assert false *)
      | [x] -> constr &&& x
      | _ -> constr &&& And eqs) en in
  let constrs = And (constr :: constrs) in

  (* Check whether it is satisfiable. *)
  if not (z3test constrs) then raise Not_found;

  let allConstrs = List.map (fun (pop, pcoef) ->
    let m = ref M.empty in
    ignore(mapFormula (renameExpr m) constrs);
    m := M.map (fun v -> "x" ^ string_of_int (new_id ())) !m;

    (* Rename all space information. *)
    let constrs = mapFormula (renameExpr m) constrs in
    let pop1 = M.fold (fun k ->
      M.add (if k = "" then "" else renameVar m k)) pop1 M.empty in
    let pcoef1 = M.map (fun v -> M.fold (fun k ->
      M.add (if k = "" then "" else renameVar m k)) v M.empty) pcoef1 in

    (* TODO: We need to consider operator equality between parameterized
       expressions (again!).  pop <---> pop1 *)

    (* Create a condition that restricts all coefficients to be the same. *)
    let eqs = List.map (fun k ->
      let [v1;v2] = List.map (M.findDefault M.empty k) [pcoef1;pcoef] in
      let eqCoef = M.filter (fun _ v -> v <> 0) (v1 -- v2) in
      Expr(EQ, eqCoef)) vars |>
      List.filter (fun x -> x <> Expr(EQ, M.empty)) |>
      distinct in
    match eqs with
      | [] -> Expr (EQ, M.empty) (* assert false *)
      | [x] -> constrs &&& x
      | _ -> constrs &&& And eqs) exprs in
  let allConstrs = reduce (&&&) (constr :: allConstrs) in

  (* Check whether it is satisfiable. *)
  if z3test allConstrs then allConstrs
  else raise Not_found
