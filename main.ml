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
            let id = string_of_int (new_id ()) in
            let pi = "p" ^ id in

            (* DEBUG: *)
            print_endline (id ^ "\t" ^ (printExpr (op, coef)));

            (* Building an coefficient mapping in terms of variables *)
            (M.fold (fun k v -> M.addDefault
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

let assignParameters assign (op, expr) =
  (M.fold (fun k v o -> if v <> 0 && M.findDefault k EQ op = LTE then
      (assert (v > 0); LTE) else o) assign EQ),
  (M.map (fun v -> M.fold (fun k v -> (+) ((
    M.findDefault k 1 assign) * v)) v 0) expr)

let rec getInterpolant sp =
    match sp with
    | Expr (pexpr, constraints) -> (
        (* DEBUG: Z3 integer programming constraint.
        print_endline (printFormula printExpr constraints); *)

        match Z3interface.integer_programming constraints with
        | Some sol ->
            (* DEBUG: Dump Z3 solution.
            print_endline ("Z3 solution: [" ^ (String.concat ", " (
            M.fold (fun k v l -> (k ^ "=" ^ (string_of_int v)) :: l) sol [])) ^ "]"); *)

            (* Construct one interpolant *)
            Some(Expr (assignParameters sol pexpr))
        | None -> None)
    | And sps -> getInterpolantList true sps
    | Or sps -> getInterpolantList false sps
and getInterpolantList opAnd sps =
    (* If the space is expressed by the union of spaces, take one interpolant from each space *)
    try
        let is = List.map (fun x ->
            match getInterpolant x with
            | Some x -> x
            | None -> raise Not_found) sps in
        Some (if opAnd then And is else Or is)
    with Not_found -> None

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
            let [v1;v2] = List.map (M.findDefault k M.empty) [coef1;coef2] in
            (Expr(EQ, v1 ++ v2) :: r1),
            (Expr(EQ, v1 -- v2) :: r2)) ([], []) vars in

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
    let plus x = M.addDefault "" 1 0 (+) x in
    let minus x = M.add "" (1 - (M.findDefault "" 0 x)) (~-- x) in

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
    match List.map (fun x -> convertToNF false (mapFormula normalizeExpr x)) formulae with
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

    (* Rename all variables into internal names to avoid name collision. *)
    let m = ref M.empty in
    let pvars = M.map (renameList m) pvars in
    let lh = M.fold (fun x v l -> Leaf(PredVar (x, v)) :: l) pvars [] in
    let lh = match la with
      | None -> lh
      | Some x -> Leaf(LinearExpr (mapFormula (renameExpr m) x)) :: lh in

    let rh = match rh with
    | PredVar (p, l) ->
        (* TODO: DEBUG: Guarantee the absence of loop structure. Will be
           supported in future version. *)
        assert (not (M.mem p pvars));

        PredVar (p, (renameList m l))
    | LinearExpr e -> LinearExpr (mapFormula (renameExpr m) e) in

    (* Make pieces of horn clause trees. *)
    (M.fold (fun x _ -> S.add x) pvars S.empty, Tree(rh, lh)) :: trees
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

      | PredVar (p, l) ->
        (* Current item is not considered for replacement because we do not
           consider looping construct at this moment. ... Well even if we do, it
           may not be a good idea to perform replacement anyway.
           By the way, `rest` and `x` is the correct order because `rest` should
           be prioritized for further processing. *)
        let replace, new_rest = List.partition (
          fun (fpvs, _) -> S.mem p fpvs) (rest @ x) in
        match replace with
        | [] ->
          (* If a predicate variable comes at the root, insert a tautological
             linear expression on top for ease of calculation. It will be later
             refuted to make a contradiction for interpolation. *)
          let current = (fpvs, Tree(LinearExpr (Expr (NEQ, M.add "" 1 M.empty)), [t])) in
          graft (x @ [current]) rest

        | [(rep_fpvs, rep_t)] ->
          let new_t = dfs ~pre:(fun dfs_t ->
            match dfs_t with
            | Leaf (PredVar (pp, ll)) ->
              if p = pp then (
                (* Replace this leaf with the current tree. Note that we can do
                   this right because we do not have loop. If we do have a
                   recursive reference of predicate variable, this replacement
                   does not end. *)

                (* We need to add a constraint to let the renamed variables equal. *)
                assert (List.length l = List.length ll);

                if List.length l = 0 then
                  t
                else
                  let eq = reduce (&&&) (List.map (fun (a, b) -> Expr (
                      EQ, M.add a 1 (M.add b (-1) M.empty))) (zip l ll)) in
                  Tree(LinearExpr (eq), [t]))
              else dfs_t
            | _ -> dfs_t) rep_t in

          (* Update free predicate variables. *)
          let rep_fpvs = (S.remove p rep_fpvs) in

          (* TODO: DEBUG: We guarantee there is no DAG for the moment. To be
             supported. *)
          assert (S.is_empty (S.inter rep_fpvs fpvs));

          let new_fpvs = S.union rep_fpvs fpvs in
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

module MyInt = struct
  type t = int
  let compare = compare
end

module MI = MapEx.Make(MyInt)

let solveTree tree =
  let laMap = ref MI.empty in
  let laId = ref 0 in
  let rootId = ref (-1) in
  let laMergeGroups = ref [] in
  let predMap = ref M.empty in
  ignore(dfs
    ~trans:(fun x -> [],
      match x with
        | LinearExpr e -> let id = incr laId; !laId in
                          `L (laMap := MI.add id e !laMap; id)
        | PredVar p -> `P p)

    ~post:(function
      | Tree((_, x), children) ->
        let (a, (merge, leaf)) = List.fold_left (
          fun (a, (merge, leaf)) (Leaf(x, y)) -> (x @ a),
            match y with
              | `L x -> merge, (
                match leaf with
                  | None -> Some x
                  | Some _ -> assert false (* Should only appear once *))
              | `LP x -> (x :: merge), leaf
              | `P _ -> merge, leaf) ([], ([], None)) children in
        let merge = match leaf with
          | Some x -> x :: merge
          | None -> merge in
        if List.length merge > 1 then
          laMergeGroups := merge :: !laMergeGroups;

        (match x with
          | `P ((p, params) as pp) ->
            predMap := M.add p (params, a) !predMap;
            Leaf(a, `P pp)
          | `L x -> rootId := x; Leaf(x :: a, `LP x)
          | `LP _ -> assert false)
      | Leaf (_, `L x) -> Leaf([x], `L x)
      | _ -> assert false (* Ditto *)) tree);

  let laMap = List.fold_right (fun (x::rest) ->
    (* Changing the root linear expression group ID, if merge occurs. *)
    if List.mem !rootId rest then rootId := x;

    predMap := M.map (fun (params, a) ->
      let (_, a) = List.fold_left (fun (_x, l) y ->
        match _x, (List.mem y rest) with
          | _, false -> (_x, y::l)
          | true, _ -> (_x, l)
          | false, _ -> (true, x::l)) (false, []) a in
      (params, a)) !predMap;

    List.fold_right (fun y laMap ->
      let _y = MI.find y laMap in
      let laMap = MI.remove y laMap in
      MI.addDefault x _y top (&&&) laMap) rest) !laMergeGroups !laMap in

  (* Before start processing, root expression should be negated to make a contradiction. *)
  let laMap = laMap |>
      (MI.add !rootId (!!! (MI.find !rootId laMap))) |>
      (MI.map ((mapFormula normalizeExpr) |- (convertToNF false))) in
  let (laIds, laDnfs) = List.split (MI.bindings laMap) in
  reduce (fun _ _ -> assert false
    (* mergeSpace (* TODO: NYI. Should consider opAnd *) *)) (
    List.map (fun assigns ->
      (* Give IDs and flatten. *)
      let exprs = listFold2 (fun t x y ->
        (List.map (fun z -> (x, z)) y) @ t) [] laIds assigns in

      (* Build the coefficient mapping for the first, and at the same time, check
         the operator of each expression. *)
      let coefMap, constrs, op, piMap =
        List.fold_left (fun (coefMap, constrs, ops, piMap) (id, (op, coef)) ->
          let strId = string_of_int (new_id ()) in
          let pi = "p" ^ strId in

          (* DEBUG: *)
          print_endline (strId ^ "\t" ^ (printExpr (op, coef)));

          (* Building an coefficient mapping in terms of variables *)
          (M.fold (fun k v -> M.addDefault
            k (pi, v) M.empty (fun m (k, v) -> M.add k v m)) coef coefMap),

          (* If the expression is an inequality, its weight should be
             positive *)
          (match op with
            | EQ -> constrs
            | LTE -> Expr(GTE, M.add pi 1 M.empty) :: constrs
            | _ -> assert false),

          (* The flag to note that the interpolant should be LTE or EQ *)
          (M.add pi op ops),

          (* Correspondance between expression ID and groupID *)
          (M.add pi id piMap)
        ) (M.empty, [], M.empty, M.empty) exprs in

      (M.map (fun (params, a) ->
        let renameMap = ref (let (_, m) = List.fold_left (fun (i, m) x -> (i + 1),
          M.add x (String.make 1 (Char.chr (97 + i))) m) (0, M.empty) params in m) in
        renameList renameMap params,
        Expr (renameExpr renameMap (op, M.map (
          M.filter (fun k _ -> List.mem (M.find k piMap) a)) coefMap))
      ) !predMap),
      And(List.rev (  (* DEBUG: rev *)
        M.fold (fun k v -> (@) [ Expr((if k = "" then
            (if constrs = [] then NEQ else GT) else EQ), v) ]) coefMap constrs))
  ) (directProduct laDnfs))

let getSolution (pexprs, constr) =
  (* DEBUG: Dump Z3 problem.
  print_endline ("Z3 problem: " ^ (printFormula printExpr constr)); *)

  match Z3interface.integer_programming constr with
    | Some sol ->
      (* DEBUG: Dump Z3 solution.
         print_endline ("Z3 solution: [" ^ (String.concat ", " (
         M.fold (fun k v l -> (k ^ "=" ^ (string_of_int v)) :: l) sol [])) ^ "]"); *)

      (* Construct one interpolant *)
      M.map (fun (params, x) -> params, (mapFormula (assignParameters sol) x)) pexprs
    | None -> raise Not_found

let preprocLefthand =
  List.fold_left (fun (pvars, la) -> function
    | LinearExpr x -> pvars, Some (match la with
        | None -> x
        | Some y -> x &&& y)
    | PredVar (p, params) -> (M.add p params pvars), la) (M.empty, None)

let solve clauses =
  let clauses = List.map (fun (lh, rh) -> (preprocLefthand lh), rh) clauses in
  let trees = buildTrees clauses in

  (* DEBUG: dump trees
  List.iter (fun t -> print_endline (printTree printHornTerm t)) trees; *)

  reduce (fun (m1, c1) (m2, c2) ->
    (M.merge (fun _ a b ->
      match a, b with
        | None, None
        | Some _, Some _ -> assert false
        | x, None
        | None, x -> x) m1 m2),
    c1 &&& c2) (List.map solveTree trees)
