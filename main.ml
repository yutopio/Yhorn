open Util
open Types

(** [any] denotes the interpolant space x=0 where x can be anything. Equivalent
    of (0=0 | 0=1). *)
let any = Expr ((M.empty, M.add "" (M.add "x" 1 M.empty) M.empty),
    Expr (EQ, M.empty))

(** [bot] denotes the interpolant space x=0 where x is not equal to 0.
    Equivalent of 0=1. *)
let bot = Expr ((M.empty, M.add "" (M.add "x" 1 M.empty) M.empty),
    Expr (NEQ, M.add "x" 1 M.empty))

(** [top] denotes the interpolant space 0=0. *)
let top = Expr ((M.empty, M.empty), Expr (EQ, M.empty))

(* Try to calculate an interpolant from given expressions. All expressions are
   to be represented as (consider : bool, (operator, coefficients : int M.t)).
   The first bool represents if the expression should be considered as the first
   logical group (in other words, to be considered when making an interpolant).
   Other parameter represents the expression. The operator should be either LTE
   or EQ. Any other are considered as LTE. *)
let getSpace exprs =
    (* Add 0 <= 1 constraint for completeness. *)
    let exprs = (true, (LTE, M.add "" (-1) M.empty)) :: exprs in

    (* DEBUG: Debug output *)
    print_endline "\nExpressions:";
    List.iter (fun (f, e) -> if f then print_endline ("\t" ^ (printExpr e))) exprs;
    print_endline "    --------------------";
    List.iter (fun (f, e) -> if not f then print_endline ("\t" ^ (printExpr e))) exprs;
    (* DEBUG: Following code snippets also shows expression numbers
    print_endline "\nExpressions:";
    let _ = List.fold_left (fun i (f, e) -> if f then print_endline (
        (string_of_int i) ^ "\t" ^ (printExpr e)); i + 1) 0 exprs in
    print_endline "    --------------------";
    let _ = List.fold_left (fun i (f, e) -> if not f then print_endline (
        (string_of_int i) ^ "\t" ^ (printExpr e)); i + 1) 0 exprs in *)

    (* Build the coefficient mapping for the first, and at the same time, check
       the operator of each expression. *)
    let m, constrs, (a, b), op =
        List.fold_left (fun (m, constrs, (a, b), ipOp) (c, (op, coef)) ->
            let pi = "p" ^ (string_of_int (new_id ())) in

            (* Building an coefficient mapping in terms of variables *)
            (M.fold (fun k v -> addDefault
                k (pi, v) M.empty (fun m (k, v) -> M.add k v m)) coef m),

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
    And(List.rev (  (* DEBUG: rev *)
        M.fold (fun k v -> (@) [ Expr((if k = "" then
            (if constrs = [] then NEQ else GT) else EQ), v) ]) m constrs))

let rec getInterpolant sp =
    let inner opAnd sps =
        (* If the space is expressed by the union of spaces, take one interpolant from each space *)
        try
            let is = List.map (fun x ->
                match getInterpolant x with
                | Some x -> x
                | None -> raise Not_found) sps in
            Some (if opAnd then And is else Or is)
        with Not_found -> None in

    match sp with
    | Expr ((op, expr), constraints) -> (
        (* DEBUG: Z3 integer programming constraint.
        print_endline (printFormula printExpr constraints); *)

        match Z3interface.integer_programming constraints with
        | Some sol ->
            (* DEBUG: Dump Z3 solution.
            print_endline ("Z3 solution: [" ^ (String.concat ", " (
            M.fold (fun k v l -> (k ^ "=" ^ (string_of_int v)) :: l) sol [])) ^ "]"); *)

            (* Construct one interpolant *)
            let expr = M.map (fun v -> M.fold (fun k v -> (+) ((
                if M.mem k sol then M.find k sol else 1) * v)) v 0) expr in
            let op = M.fold (fun k v o -> if v <> 0 && M.mem k op && M.find k op = LTE then
                (assert (v > 0); LTE) else o) sol EQ in
            Some (Expr (op, expr))
        | None -> None)

    | And sps -> inner true sps
    | Or sps -> inner false sps

(* DEBUG: Uncomment following lines to dump intermediate interpolants
let getInterpolant sp =
    let ret = getInterpolant sp in
    (match ret with
      | Some x -> print_endline (printFormula printExpr x)
      | None -> print_endline "none");
    ret *)

let rec mergeSpace opAnd sp1 sp2 =
    let mergeSpSp ((op1, coef1), And c1) ((op2, coef2), And c2) =

        (* Consider all variables are present in both *)
        let x1 = M.fold (fun k v r -> k :: r) coef1 [] in
        let x2 = M.fold (fun k v r -> k :: r) coef2 [] in
        let vars = distinct (x1 @ x2) in

        (* Coefficients of both interpolants must be the same *)
        let (c3, c4) = List.fold_left (fun (r1, r2) k ->
            let v1 = if M.mem k coef1 then M.find k coef1 else M.empty in
            let v2 = if M.mem k coef2 then M.find k coef2 else M.empty in
            (let v = coefOp (+) v1 v2 in Expr(EQ, v) :: r1),
            (let v = coefOp (-) v1 v2 in Expr(EQ, v) :: r2)) ([], []) vars in

        (* DEBUG: rev is for ease of inspection *)
        let c3, c4 = (List.rev c3), (List.rev c4) in

        (* Check weight variables those for making an interpolant LTE rather
           than EQ. Note i1eq = ~i1lte and i2eq = ~i2lte. *)
        let f x =
            let p = ref [] in
            M.iter (fun k v -> if v = LTE then p := k :: !p) x;
            let eq, neq = List.fold_left (fun (c1, c2) x ->
                ((Expr (EQ, M.add x 1 M.empty)) :: c1),
                ((Expr (NEQ, M.add x 1 M.empty)) :: c2)) ([], []) !p in
            (!p, eq, neq) in
        let (p1lte, i1eq, i1lte), (p2lte, i2eq, i2lte) = (f op1), (f op2) in

        (* Constraint for making both interpolant the same operator. *)
        let c5 = match p1lte, p2lte with
            | [], [] -> [ Or [ And c3; And c4 ] ]
            | _, [] -> (Or [ And c3; And c4 ]) :: i1eq
            | [], _ -> (Or [ And c3; And c4 ]) :: i2eq
            | _, _ -> [ Or ((And i2eq) :: i1lte); Or ((And i1eq) :: i2lte);
                Or ([ And c3; And c4 ] @ i1lte); Or [ And i1eq; And c4 ] ] in

          let sp = ((M.fold M.add op1 op2), coef1), (And (c1 @ c2 @ c5)) in
        match getInterpolant (Expr sp) with
        | Some _ -> Expr sp
        | None ->
            if opAnd then
                (* (* If failed to merge space for And, there is no interpolant. *)
                Expr ((M.empty, M.empty), Expr(EQ, M.add "" 1 M.empty)) *)
                And [ sp1; sp2]
            else Or [ sp1; sp2 ] in

    let mergeSpSps sp sps spsAnd =
        (* Try to take simple intersection between each space and one. When
           successful, newly created spaces will be concatenated. Otherwise,
           just add one space into the list. *)
        try
            let sps = List.map (fun sp1 ->
                match (mergeSpace opAnd sp sp1), opAnd with
                | Expr x, _ -> Expr x
                | And _, true
                | Or _, false -> raise Not_found
                | _ -> assert false) sps in
            if spsAnd then And sps else Or sps
        with Not_found -> (
            match opAnd, spsAnd with
            | true, true -> And (sp :: sps)
            | true, false -> And [ sp; Or sps ]
            | false, true -> Or [ sp; And sps ]
            | false, false -> Or (sp :: sps)) in

    match sp1, sp2, opAnd with
    | Expr e1, Expr e2, _ -> mergeSpSp e1 e2
    | And sps, Expr e, _
    | Expr e, And sps, _ -> mergeSpSps (Expr e) sps true
    | And sps1, And sps2, true -> And (sps1 @ sps2)
    | Or sps, Expr e, _
    | Expr e, Or sps, _ -> mergeSpSps (Expr e) sps false
    | Or sps1, Or sps2, false -> Or (sps1 @ sps2)
    | And sps_a, Or sps_o, true
    | Or sps_o, And sps_a, true -> And ((Or sps_o) :: sps_a)
    | And sps_a, Or sps_o, false
    | Or sps_o, And sps_a, false -> Or ((And sps_a) :: sps_o)
    | _, _, true -> And [ sp1; sp2 ]
    | _, _, false -> Or [ sp1; sp2 ]

let laSolve a b =
    let filter op = List.filter (fun (x, _) -> x = op) in
    let addFlag op exprs consider = List.map (fun x -> (consider, x)) (filter op exprs) in
    let proc op exprs consider = let t = addFlag op exprs consider in (t, List.length t) in
    let exec = fun x -> x () in

    (* Extract all equations and not-equal inequations *)
    let eqA, leqA = proc EQ a true in
    let neqA, lneqA = proc NEQ a true in
    let eqB, leqB = proc EQ b false in
    let neqB, lneqB = proc NEQ b false in
    let plus x = addDefault "" 1 0 (+) x in
    let minus x = M.add "" (1 - (if M.mem "" x then M.find "" x else 0)) (~-- x) in

    let tryGetInterpolant opAnd exprs = tryPick (fun (consider, (_, coef)) ->
        (* DEBUG: List.rev is for ease of inspection *)
        let sp1 = Expr(getSpace (List.rev ((consider, (LTE, plus coef)) :: exprs))) in
        match getInterpolant sp1 with None -> None | Some _ ->
        let sp2 = Expr(getSpace (List.rev ((consider, (LTE, minus coef)) :: exprs))) in
        match getInterpolant sp2 with None -> None | Some _ ->
        Some(mergeSpace opAnd sp1 sp2)) in

    let none _ = None in

    let eqAeqB _ =
        let eqs = eqA @ eqB in
        tryPick exec [
            (fun _ -> tryGetInterpolant false eqs neqA);
            (fun _ -> tryGetInterpolant true eqs neqB) ] in
    let eqAneqB _ = tryGetInterpolant true eqA neqB in
    let neqAeqB _ = tryGetInterpolant false eqB neqA in

    let eqAll _ =
        let sp = Expr(getSpace ((List.map (fun x -> true, x) a) @ (List.map (fun x -> false, x) b))) in
        match getInterpolant sp with None -> None | Some _ -> Some sp in

    let all _ =
        (* Gather all expressions of LTE with consideration flag. *)
        let exprs = (addFlag LTE a true) @ (addFlag LTE b false) @ (eqA @ eqB) in

        (* Split not-equal inequations into disjunction of two expressions and
           choose either as for each inequations. *)
        let neqExpand = List.map (fun (c, (_, coef)) ->
            [ (c, (LTE, plus coef)) ; (c, (LTE, minus coef)) ]) in
        let neqAs = directProduct (neqExpand neqA) in
        let neqBs = directProduct (neqExpand neqB) in

        (* Try to get interpolant *)
        try
            Some (
            reduce (mergeSpace true) (List.map (fun b ->
            reduce (mergeSpace false) (List.map (fun a ->
                let sp = Expr (getSpace (exprs @ a @ b)) in
                match getInterpolant sp with
                | Some _ -> sp
                | None -> raise Not_found) neqAs)) neqBs))
        with Not_found -> None in

    tryPick exec [
        (if leqA <> 0 then (if leqB <> 0 then eqAeqB else eqAneqB) else neqAeqB);
        (if lneqA + lneqB = 0 then eqAll else none);
        all]

let interpolate formulae = try (
    match List.map (fun x -> convertToNF false (normalizeFormula x)) formulae with
    | [a_s; b_s] -> (
        try
            (* Remove contradictory conjunctions. *)
            let removeContradiction l =
                List.rev (List.fold_left (fun l x -> match laSolve x [] with
                  | Some _ -> l
                  | None -> x :: l) [] l) in
            let a_s = removeContradiction a_s in
            let b_s = removeContradiction b_s in

            Some (match a_s, b_s with
            | [], [] -> any
            | [], _ -> bot
            | _, [] -> top
            | _, _ ->

            (* Calculate the interpolant space between each conjunctions from A
               and B. *)
            let spaces = List.map (fun b -> List.map (fun a ->
                match laSolve a b with
                | Some x -> x
                | None -> raise Not_found) a_s) b_s in

(* DEBUG: Copied from util.ml in VHorn *)
let rec transpose xss = (
  if List.for_all (fun xs -> xs = []) xss then
    []
  else
    let xs, xss =
      List.split
        (List.map (function x::xs -> x, xs | _ -> assert false ) xss)
    in
    xs::transpose xss) in
(*************************************************)

            let cnf = reduce (mergeSpace true) (
                List.map (reduce (mergeSpace false)) spaces) in
            let dnf = reduce (mergeSpace false) (
                List.map (reduce (mergeSpace true)) (transpose spaces)) in
            if countFormula cnf > countFormula dnf then dnf else cnf)
        with Not_found -> None)
    | _ -> assert false (* TODO: NYI *)

    ) with e ->
        print_endline ("Yint: Unhandled exception (" ^
            (Printexc.to_string e) ^
            ")");
        assert false

(* TODO: Consider moving to types.ml *)
type 'a tree =
  | Tree of 'a * 'a tree list
  | Leaf of 'a

let printTree eltPrinter t =
  let buf = Buffer.create 1 in
  let print i x = Buffer.add_string buf (i ^ (eltPrinter x) ^ "\n") in
  let rec printTree indent = function
    | Leaf x -> print indent x
    | Tree (x, children) -> print indent x;
      List.iter (printTree (indent ^ "  ")) children in
  printTree "" t;
  Buffer.contents buf

let id x = Obj.magic x
let rec dfs ?(pre=id) ?(post=id) ?(trans=id) tree =
  let dfs = dfs ~pre:pre ~post:post ~trans:trans in
  let elt = pre tree in
  post (match elt with
  | Tree(x, children) -> Tree((trans x), (List.map dfs children))
  | Leaf x -> Leaf (trans x))

(* TODO: Rename this. *)
let top = Expr (EQ, M.empty)
let bot = Expr (EQ, M.add "" 1 M.empty)

let buildTrees clauses =
  (* TODO: If you consider solving Horn clauses with complicated structure, it
     may be a good idea to consider using Ocamlgraph. *)
  let buildSeedling = List.fold_left (fun trees (lh, rh) ->
    let (pvars, la) = lh in
    let lh = SP.fold (fun x l -> Leaf(PredVar x) :: l) pvars [] in
    let lh = match la with
      | None -> lh
      | Some x -> Leaf(LinearExpr x) :: lh in

    (* TODO: DEBUG: Guarantee the absence of loop structure. Will be supported
       in future version. *)
    (match rh with
    | PredVar p -> assert (not (SP.mem p pvars))
    | _ -> ());

    (* Make pieces of horn clause trees. *)
    (pvars, Tree(rh, lh)) :: trees
  ) [] in

  (* TODO: Very inefficient algorithm to build a tree. *)
  let rec graft x = function
    | [] -> x
    | current :: rest ->
      let (fpvs, (Tree(rh, lh) as t)) = current in

      match rh with
      | LinearExpr _ ->
        (* Skip. Linear expression always comes at the root. *)
        graft (x @ [current]) rest

      | PredVar p ->
        (* Current item is not considered for replacement because we do not
           consider looping construct at this moment. ... Well even if we do, it
           may not be a good idea to perform replacement anyway.
           By the way, `rest` and `x` is the correct order because `rest` should
           be prioritized for further processing. *)
        let replace, new_rest = List.partition (
          fun (fpvs, _) -> SP.mem p fpvs) (rest @ x) in
        match replace with
        | [] ->
          (* If a predicate variable comes at the root, insert contradictory
             linear expression on top for ease of calculation. *)
          let current = (fpvs, Tree(LinearExpr bot, [t])) in
          graft (x @ [current]) rest

        | [(rep_fpvs, rep_t)] ->
          let new_t = dfs ~pre:(fun dfs_t ->
            match dfs_t with
            | Leaf (PredVar pp) ->
              if p = pp then
                (* Replace this leaf with the current tree. Note that we can do
                   this right because we do not have loop. If we do have a
                   recursive reference of predicate variable, this replacement
                   does not end. *)
                t
              else dfs_t
            | _ -> dfs_t) rep_t in

          (* Update free predicate variables. *)
          let rep_fpvs = (SP.remove p rep_fpvs) in

          (* TODO: DEBUG: We guarantee there is no DAG for the moment. To be
             supported. *)
          assert (SP.is_empty (SP.inter rep_fpvs fpvs));

          let new_fpvs = SP.union rep_fpvs fpvs in
          let current = (new_fpvs, new_t) in
          graft [] (new_rest @ [current])
        | _ ->
          (* TODO: We still do not support DAG (Directed acyclic graph)
             structure. *)
          assert false in

  (* Eliminate free variable information. *)
  let _, trees = List.split (graft [] (buildSeedling clauses)) in
  List.map (dfs ~pre:(fun t ->
    match t with
    | Leaf (PredVar pp as p) ->
      (* If a predicate variable comes at leafs, insert tautological linear
         expression for ease of calculation. *)
      Tree(p, [ Leaf (LinearExpr top) ])
    | _ -> t)) trees

let solveTree tree =
  (* Preprocess tree to add a placeholder for linear expressions propagation. *)
  let tree = dfs ~trans:(fun x -> bot, x) tree in

  let m = ref MP.empty in
  ignore(dfs
    ~pre:(function
      | Tree((exprs, x), children) ->
        (* Gather leaves from the children level. *)
        let leaves = List.fold_left (fun l x ->
          match x with
          | Leaf(_, LinearExpr e) -> e :: l
          | _ -> l) [] children in

        (* DEBUG: Should be at most one leave... *)
        assert (List.length leaves <= 1);

        (* By combining leaves from above and the root, build an expression
           for the second group of interpolation input. *)
        let childExprs = reduce (&&&) ((
          match x with
          | LinearExpr e -> e (* Only the root. *)
          | _ -> exprs) :: leaves) in

        (* Propagate leave information to decendants. *)
        let newChildren = List.map (fun x ->
          match x with
          | Tree((_, x), children) ->
            Tree((childExprs, x), children)
          | _ -> x) children in

        (* Renew current node. *)
        Tree((exprs, x), newChildren)
      | Leaf (_, LinearExpr e) -> Leaf (bot, LinearExpr e) (* Don't care *)
      | _ -> assert false (* No predicate variables comes at leaves. *))

    ~post:(function
      | Tree((_, LinearExpr e), _) -> Leaf(bot, LinearExpr bot) (* Don't care *)
      | Tree((b, PredVar p), children) ->
        let a = reduce (&&&) (List.map (fun (Leaf(x, _)) -> x) children) in
        m := MP.add p (a, b) !m;
        Leaf (a, LinearExpr bot)
      | Leaf (_, LinearExpr e) -> Leaf(e, LinearExpr bot)
      | _ -> assert false (* Ditto *)) tree);

  (* Perform interpolation to give predicates to all variables. *)
  MP.map (fun (a, b) -> (interpolate [a;b])) !m

let solve clauses =
  let trees = buildTrees clauses in
  List.fold_left (fun m t ->
    (* DEBUG: dump trees *)
    print_endline (printTree printHornTerm t);

    MP.merge (fun _ a b ->
    match a, b with
    | None, None
    | Some _, Some _ -> assert false
    | x, None
    | None, x -> x) m (solveTree t)) MP.empty trees
