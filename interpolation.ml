open Util
open Types
open Constr

exception Satisfiable of (Id.t * int) list

type space = pexpr nf * constrSet

(* Try to calculate an interpolant from given expressions. All expressions are
   to be represented as (consider : bool, (operator, coefficients : int M.t)).
   The first bool represents if the expression should be considered as the first
   logical group (in other words, to be considered when making an interpolant).
   Other parameter represents the expression. The operator should be either LTE
   or EQ. Any other are considered as LTE. *)
let interpolateSimple exprs =
  (* Add 0 <= 1 constraint for completeness. *)
  let exprs = (true, (LTE, M.add Id.const (-1) M.empty)) :: exprs in

  (* Build the coefficient mapping for the first, and at the same time, check
     the operator of each expression. *)
  let m, constrs, (a, b), op =
    List.fold_left (fun (m, constrs, (a, b), ipOp) (c, (op, coef)) ->
      let pi = Id.create () in

      (* Building an coefficient mapping in terms of variables *)
      (M.fold (fun k v -> M.addDefault
        M.empty (fun m (k, v) -> M.add k v m) k (pi, v)) coef m),

      (* If the expression is an inequality, its weight should be
         positive *)
      (match op with
        | EQ -> constrs
        | LTE -> Expr(GTE, M.add pi 1 M.empty) :: constrs
        | _ -> assert false),

      (* To build the coefficient mapping for an interpolant, the variable
         name for the weight of each expression should be memorized *)
      (if c then (pi :: a), b else a, (pi :: b)),

      (* The flag to note that the interpolant should be LTE or EQ *)
      (if c then M.add pi op ipOp else ipOp))
      (M.empty, [], ([], []), M.empty) exprs in

  (* The interpolant will be a sum among some expressions *)
  (op, M.map (M.filter (fun k _ -> List.mem k a)) m),

  (* In constraints, all variables' coefficients must be equals to zero under
     given weights to each expression. As for the constants, if all expression
     were equalities, the sum of them must be not equal (NEQ) to zero to make
     inconsistency. Otherwise, i.e., LTE inequalities involved, the sum must
     be greater than zero. *)
  And(M.fold (fun k v c -> Expr(
    (if k = Id.const then if constrs = [] then NEQ else GT else EQ), v)::c) m constrs)

let getInterpolant (pexpr, constrSet) =
  (* We don't specify max size for a unification template, so None must not
     occur. *)
  let Some (pexpr, constrs) = Template.unify Unify.equal constrSet [ pexpr ] in
  let sol = Constr.solve constrs in
  let ret = List.map (List.map (fun pexpr ->
    normalizeExpr (HornGet.assignParameters sol pexpr))) pexpr in
  convertToFormula true ret

let interpolate (a, b) =
  try (
    let [a_s; b_s] = List.map (
      mapFormula normalizeExpr |-
      splitNegation |-
      convertToNF false |-

      (* Remove contradictory conjunctions. *)
      List.filter (fun x ->
        let x = List.map (fun x -> Expr x) x in
        Z3interface.check_formula (And x) <> Some false)) [a; b] in

    match a_s, b_s with
      | [], [] ->
        (* Returns the interpolant space x=0 where x can be anything.
           Equivalent of (0=0 | 0=1). *)
        [[M.empty, M.add Id.const (M.add (Id.create ()) 1 M.empty) M.empty]],
        ([], Puf.create 0, MI.empty)
      | [], _ ->
        (* Returns the interpolant space x=0 where x is not equal to 0.
           Equivalent of 0=1. *)
        (* TODO: Sentinel method is not a good idea!! *)
        let x = Id.create () in
        [[M.empty, M.add Id.const (M.add x 1 M.empty) M.empty]],
        ([x], Puf.create 1, MI.add 0 (Expr (NEQ, M.add x 1 M.empty)) MI.empty)
      | _, [] ->
        (* Returns the interpolant space 0=0. *)
        [[M.empty, M.empty]], ([], Puf.create 0, MI.empty)
      | _, _ ->
        (* Calculate the interpolant space between each conjunctions from A and
           B. *)
        let constrs = ref [] in
        let pexprCnf = List.map (fun b -> List.map (fun a ->
          (* Satisfiability check. *)
          (match Z3interface.integer_programming (
            And (List.map (fun x -> Expr x) (a @ b))) with
            | Some x -> raise (Satisfiable (M.bindings x))
            | _ -> ());

          let a = List.map (fun x -> true, x) a in
          let b = List.map (fun x -> false, x) b in
          let pexpr, constr = interpolateSimple (a @ b) in
          constrs := (Id.create () (* sentinel *), constr) :: !constrs;
          pexpr
        ) a_s) b_s in
        let ids, constrs = List.rev !constrs |> List.split in
        let puf = Puf.create (List.length constrs) in
        let _, constrs = List.fold_left (fun (i, m) x -> i + 1, MI.add i x m)
          (0, MI.empty) constrs in
        pexprCnf, (ids, puf, constrs)
  ) with
    | Satisfiable x as e -> raise e
    | e ->
      print_endline ("Yint: Unhandled exception (" ^
                        (Printexc.to_string e) ^ ")");
      assert false

let verifyInterpolant input output =
  (* Check of free variable. *)
  let a_s, b_s = input in
  let [va; vb; vI] =
    List.map (fun x ->
      let m = ref M.empty in
      ignore (mapFormula (renameExpr m) x);
      M.keys !m)
      [ a_s; b_s; output] in
  let usable = List.filter (fun x -> List.exists ((=) x) va) vb in
  assert (List.for_all (fun x -> List.exists ((=) x) usable) vI);

  (* Logical check. *)
  assert (Z3interface.check_interpolant input output);

  (* Test passed. *)
  ()
