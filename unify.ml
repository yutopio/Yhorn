open ListEx
open Util
open Types

(* Test wether the constraint is satisfiable or not. *)
let z3test x = try ignore (Z3interface.solve ["", x]); true with _ -> false

(** Unification algorithm for interpolants. *)
let equal pexprs constrSet =
  (* Make a constraint for unifing interpolants with all coefficients equal. *)
  if List.length pexprs = 1 then constrSet else (

  assert (List.length pexprs >= 2);

  (* Consider all variables are present in all pexprs. *)
  let vars =
    List.fold_left (fun l (_, coef) -> (M.keys coef) @ l) [] pexprs |>
    sort_distinct in

  let f (op1, coef1) l (op2, coef2) =
    (* Coefficients of both interpolants must be the same *)
    let (c1, c2) = List.fold_left (fun (r1, r2) k ->
      let [v1;v2] = List.map (M.findDefault M.empty k) [coef1;coef2] in
      (Expr(EQ, v1 ++ v2) :: r1),
      (Expr(EQ, v1 -- v2) :: r2)) ([], []) vars in

    (* Check weight variables those for making an interpolant LTE. *)
    let f x =
      M.fold (fun k v p -> if v = LTE then k :: p else p) x [] |>
      List.fold_left (fun c x -> (Expr (EQ, M.add x 1 M.empty)) :: c) [] in
    let i1eq, i2eq = (f op1), (f op2) in

    let [c1;c2;i1eq;i2eq] = List.map (fun x -> And x) [c1;c2;i1eq;i2eq] in

    (* Constraint for making both interpolant the same operator. *)
    let has_eq = i1eq ||| i2eq in
    (i1eq <=> i2eq) :: (i1eq ==> (c1 ||| c2)) :: (!!! i1eq ==> c2) :: l in

  let rec fold ret = function
    | x::(_::_ as l) -> fold (List.fold_left (f x) ret l) l
    | [_] -> ret
    | _ -> assert false in
  let additional = And (fold [] pexprs) in

  let pvarIds =
    List.map Constr.pollPVarId pexprs |>
    List.filter ((<>) None) |>
    List.map (fun (Some x) -> x) in
  match pvarIds with
    | [] -> constrSet
    | _ ->
      let newId, (ids, puf, constrs) = Constr.mergeConstrs pvarIds constrSet in
      let constr = MI.find (Puf.find puf newId) constrs in
      let constr = constr &&& additional in

      (* Check whether it is satisfiable. *)
      if not (z3test constr) then raise Not_found;

      let constrs = MI.add (Puf.find puf newId) constr constrs in
      ids, puf, constrs)

let generatePexprUnifyConstr exprs constr =
  assert (List.length exprs >= 2);

  (* Consider all variables are present in both. *)
  let vars = List.fold_left (fun l (_, pcoef) ->
    (M.fold (fun k _ r ->
      if List.exists ((=) k) r then r else k :: r) pcoef l)) [] exprs in

  let (pop1,pcoef1)::en = exprs in
  let constrs = List.map (fun (pop, pcoef) ->
    let m = ref M.empty in

    (* Rename all space information. *)
    let constr = mapFormula (renameExpr m) constr in
    let pop = M.fold (fun k ->
      M.add (renameVar m k)) pop M.empty in
    let pcoef = M.map (fun v -> M.fold (fun k ->
      M.add (renameVar m k)) v M.empty) pcoef in

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

    (* Rename all space information. *)
    let constrs = mapFormula (renameExpr m) constrs in
    let pop1 = M.fold (fun k ->
      M.add (renameVar m k)) pop1 M.empty in
    let pcoef1 = M.map (fun v -> M.fold (fun k ->
      M.add (renameVar m k)) v M.empty) pcoef1 in

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
  let allConstrs = List.reduce (&&&) allConstrs in

  (* Check whether it is satisfiable. *)
  if z3test (constr &&& allConstrs) then allConstrs
  else raise Not_found
