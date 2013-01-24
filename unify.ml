open Util
open Types

let generatePexprUnifyConstr ?(nl=false) (op1, coef1) (op2, coef2) =
  (* Consider all variables are present in both *)
  let vars = [] |>
    M.fold (fun k v r -> k :: r) coef1 |>
    M.fold (fun k v r -> k :: r) coef2 |>
    distinct in

  (* Generate auxiliary variables. *)
  let q1, q2 =
    let f () = "q" ^ string_of_int (new_id ()) in
    f (), f () in
  let c3 = Expr(GT , M.add q1 1 M.empty) in (* q1  > 0 *)
  let c1 = Expr(NEQ, M.add q2 1 M.empty) in (* q2 != 0 *)
  let c2 = Expr(GT , M.add q2 1 M.empty) in (* q2  > 0 *)

  (* Coefficients of both interpolants must be the same *)
  let mul v coef = M.fold (fun k -> M.add (
    if k = "" then v else k ^ "*" ^ v)) coef M.empty in
  let c3,c4,c5 = List.fold_left (fun (r1,r2,r3) k ->
    let [v1;v2] = List.map (M.findDefault M.empty k) [coef1;coef2] in
    (Expr(EQ, v1 ++ v2) :: r1),
    (Expr(EQ, v1 -- v2) :: r2),
    (Expr(EQ, (mul q1 v1) -- (mul q2 v2)) :: r3)) ([],[],[c3]) vars in

  (* Check weight variables those for making an interpolant LTE. *)
  let f x =
    let p = M.fold (fun k v p -> if v = LTE then k :: p else p) x [] in
    let eq = List.fold_left (fun c x ->
      (Expr (EQ, M.add x 1 M.empty)) :: c) [] p in
    (p, eq) in
  let (p1lte, i1eq), (p2lte, i2eq) = (f op1), (f op2) in

  let [c3;c4;c5;i1eq;i2eq] = List.map (fun x -> And x) [c3;c4;c5;i1eq;i2eq] in

  (* Constraint for making both interpolant the same operator. *)
  if not nl then
    match p1lte, p2lte with
      | [], [] -> c3 ||| c4
      | _, [] -> (c3 ||| c4) &&& i1eq
      | [], _ -> (c3 ||| c4) &&& i2eq
      | _ -> (i1eq <=> i2eq) &&& (i1eq ==> (c3 ||| c4)) &&& ((!!! i1eq) ==> c4)
  else
    match p1lte, p2lte with
      | [], [] -> c1 &&& c5
      | _, [] -> c1 &&& c5 &&& i1eq
      | [], _ -> c1 &&& c5 &&& i2eq
      | _ -> c5 &&& (i1eq <=> i2eq) &&& (i1eq ==> c1) &&& ((!!!i1eq) ==> c2)
