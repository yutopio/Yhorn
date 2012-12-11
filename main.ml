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

let generatePexprMergeConstr (op1, coef1) (op2, coef2) =
  (* Consider all variables are present in both *)
  let vars = [] |>
    M.fold (fun k v r -> k :: r) coef1 |>
    M.fold (fun k v r -> k :: r) coef2 |>
    distinct in

  (* Coefficients of both interpolants must be the same *)
  let (c3, c4) = List.fold_left (fun (r1, r2) k ->
    let [v1;v2] = List.map (M.findDefault k M.empty) [coef1;coef2] in
    (Expr(EQ, v1 ++ v2) :: r1),
    (Expr(EQ, v1 -- v2) :: r2)) ([], []) vars in

  (* Check weight variables those for making an interpolant LTE. *)
  let f x =
    let p = M.fold (fun k v p -> if v = LTE then k :: p else p) x [] in
    let eq = List.fold_left (fun c x ->
      (Expr (EQ, M.add x 1 M.empty)) :: c) [] p in
    (p, eq) in
  let (p1lte, i1eq), (p2lte, i2eq) = (f op1), (f op2) in

  let [c3;c4;i1eq;i2eq] = List.map (reduce (&&&)) [c3;c4;i1eq;i2eq] in

  (* Constraint for making both interpolant the same operator. *)
  match p1lte, p2lte with
    | [], [] -> c3 ||| c4
    | _, [] -> (c3 ||| c4) &&& i1eq
    | [], _ -> (c3 ||| c4) &&& i2eq
    | _ -> (i1eq <=> i2eq) &&& (i1eq ==> (c3 ||| c4)) &&& ((!!! i1eq) ==> c4)

let rec mergeSpace opAnd sp1 sp2 =
    let mergeSpSp ((op1, coef1), c1) ((op2, coef2), c2) =
        let c5 = generatePexprMergeConstr (op1, coef1) (op2, coef2) in
        let sp = ((M.fold M.add op1 op2), coef1), (c1 &&& c2 &&& c5) in
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
    let plus x = M.addDefault 0 (+) "" 1 x in
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
    match List.map (
      mapFormula normalizeExpr |-
      splitNegation |-
      convertToNF false) formulae with
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

let buildGraph clauses =
  let predVertices = ref M.empty in
  List.fold_left (fun g (lh, rh) ->
    (* Rename all variables to internal names for avoiding name collision. *)
    let nameMap = ref M.empty in

    let src = match rh with
      | PredVar (p, l) ->
        if M.mem p !predVertices then (
          (* If the predicate `p` already exists, build a renaming map so that
             the current horn clause become consistent with already built part
             of the graph. *)
          let src = M.find p !predVertices in
          let PredVar (_, binders) = G.V.label src in
          nameMap := listFold2 (fun m a b -> M.add a b m) M.empty l binders;
          src
        ) else (
          (* Otherwise, create a new predicate vertex and remember it. *)
          let src = G.V.create (PredVar (p, (renameList nameMap l))) in
          predVertices := M.add p src !predVertices;
          src)
      | LinearExpr e ->
        (* If the right-hand of the horn clause is a linear expression, there
           are no special things to consider. Just create a new vertex. *)
        G.V.create (LinearExpr (mapFormula (renameExpr nameMap) e)) in

    (* Following statement has no effect if the vertex `src` is in the graph. *)
    let g = G.add_vertex g src in

    let (pvars, la) = lh in
    let g, dsts = List.fold_left (fun (g, dsts) (p, args) ->
      (* Get (or create if needed) the predicate variable vertex and its binder.
         We will relate this vertex from newly-created predicate variable
         vertices that corrensponds to the application of such predicates. The
         edge will carry binding information. *)
      let dst, binders =
        if M.mem p !predVertices then
          (* If exists, extract binders from the vertex label. *)
          let dst = M.find p !predVertices in
          let PredVar (_, binders) = G.V.label dst in
          dst, binders
        else (
          (* If not yet exists, create a new vertex with a fresh binder. *)
          let binders = repeat (fun _ l -> (new_name ()) :: l)
            (List.length args) [] in
          let dst = G.V.create (PredVar (p, binders)) in
          predVertices := M.add p dst !predVertices;
          dst, binders) in

      (* Create a vertex which corresponds to the application to the predicate
         variable. *)
      let args = renameList nameMap args in
      let src = G.V.create (PredVar (p, args)) in

      (* Build a name mapping between referred predicate variable (appears on
         the right-hand of Horn clause) and referring one (on the left-hand). *)
      let renames = listFold2 (fun l a b -> (a, b) :: l) [] binders args in

      (* Add a edge between origin *)
      let g = G.add_edge_e g (G.E.create src (Some renames) dst) in
      g, (src :: dsts)
    ) (g, []) pvars in

    (* If a linear expression exists on the left-hand, create a corresponding
       vertex. *)
    let dsts = match la with
      | None -> dsts
      | Some x ->
        (G.V.create (LinearExpr (mapFormula (renameExpr nameMap) x))) :: dsts in

    (* Add edges between all left-hand terms and right-hand term. *)
    List.fold_left (fun g dst -> G.add_edge g src dst) g dsts
  ) G.empty clauses

let top = Expr (EQ, M.empty)

let flattenGraph g =
  G.fold_vertex (fun v l ->
    (* TODO: This algorithm cannot find the self-looping predicate variable node
       which has no children. *)
    if G.in_degree g v = 0 then v :: l else l) g [] |>

  (* Traverse the graph from given starting points to make trees. *)
  List.map (fun v ->
    (* Keep track of linear expressions with giving a unique ID. *)
    let laGroups = ref MI.empty in

    (* After splitting a graph into a tree, one predicate variable may appear
       multiple times in the tree. Thus, each appearance will be remembered by
       the ID. `predMap` tracks the mapping between such predicate ID and linear
       expression IDs appearing above the predicate. `predCopies` remembers the
       correspondance between the original name of predicate variable and
       predicate IDs. *)
    let predMap = ref MI.empty in
    let predCopies = ref M.empty in

    let rec f v nameMap =
      let renamedLabel v = renameHornTerm nameMap (G.V.label v) in

      let (u's, la) = G.fold_succ (fun u (u's, la) ->
        match renamedLabel u with
          | PredVar (p, args) ->
            (* This prevents `nameMap` to be shared over all DFS. *)
            let nameMap = ref (!nameMap) in

            (* Every application vertex must have exactly one parent. *)
            let es = G.fold_succ_e (fun e l -> e :: l) g u [] in
            let e = assert (List.length es = 1); List.hd es in

            (* Bindings of predicate variables are converted to linear equations
               so that it can be treated easy. Note that the binder and argument
               will have different names even if they have the same one before
               conversion.*)
            let dst, (Some bindings) = (G.E.dst e), (G.E.label e) in
            let constr = List.fold_left (fun constr (x, y) ->
              let x' = new_name () in
              let y' = renameVar nameMap y in
              nameMap := M.add x x' !nameMap;
              Expr (EQ, M.add x' 1 (M.add y' (-1) M.empty)) :: constr)
              [] bindings in

            (* Traverse children first to unify predicate variable nodes. *)
            let u' = f dst nameMap in
            (u' @ u's), (if constr = [] then la else la &&& And(constr))

          | LinearExpr e ->
            (* NOTE: Linear expressions must appear only once. *)
            u's, (la &&& e)
      ) g v ([], top) in

      let registerLa la =
        let key = MI.cardinal !laGroups in
        laGroups := MI.add key la !laGroups; key in

      match (renamedLabel v) with
        | PredVar (p, param) ->
          let pid = (new_id ()) in
          let u's = if la <> top then (registerLa la) :: u's else u's in
          predMap := MI.add pid (param, u's) !predMap;
          predCopies := M.addDefault [] (fun l x -> x :: l) p pid !predCopies;
          u's

        | LinearExpr e ->
          (* NOTE: The vertex 'v' must be the root of traversal. *)
          registerLa (if la <> top then la &&& (!!! e) else !!! e);
          [] (* Doesn't care on what to return. *)
    in
    ignore(f v (ref M.empty));
    !laGroups, !predMap, !predCopies)

let getSolution (pexprs, constr) =
  (* DEBUG: Dump Z3 problem.
  print_endline ("Z3 problem: " ^ (printFormula printExpr constr)); *)

  match Z3interface.integer_programming constr with
    | Some sol ->
      (* DEBUG: Dump Z3 solution.
      print_endline ("Z3 solution: [" ^ (String.concat ", " (
        M.fold (fun k v l -> (k ^ "=" ^ (string_of_int v))::l) sol [])) ^ "]\n"); *)

      (* Construct one interpolant *)
      M.map (fun (params, cnf) ->
        let x = convertToFormula true cnf in
        params, (mapFormula (assignParameters sol) x)) pexprs
    | None ->
      print_endline "Unsatisfiable problem.";
      raise Not_found

let merge (sols, predMap, predCopies) =
  let predSols, constrs = List.fold_left (fun (predSolsByPred, constrs)
    (dnfChoice, predSolsByDnf, constr) ->
      MI.fold (fun pid ->
        MI.addDefault ([], MIL.empty) (fun (_, m) (param, pexpr) -> param,
          let groupKey =
            (MI.fold (fun k v l ->
              if List.mem k (MI.find pid predMap) then l
              else (k, v) :: l) dnfChoice []) |>
            (List.sort comparePair) |>
            List.split |> snd in
          MIL.addDefault [] (fun l x -> x :: l) groupKey pexpr m
        ) pid) predSolsByDnf predSolsByPred,
      constr :: constrs
  ) (MI.empty, []) sols in

  let predSols = MI.map (fun (param, pexpr) -> param,
    MIL.fold (fun _ v l -> v :: l) pexpr []) predSols in

  (M.map (fun x ->
    reduce (fun (p1, e1) (p2, e2) -> assert (p1 = p2); (p1, e1 @ e2))
      (List.map (fun x -> MI.find x predSols) x)) predCopies),
  reduce (&&&) constrs

let solveTree (laGroups, predMap, predCopies) =
  let (laIds, laDnfs) = laGroups |>
      MI.add (-1) (Expr (LTE, M.add "" (-1) M.empty)) |>
      MI.map (
        mapFormula normalizeExpr |-
        splitNegation |-
        convertToNF false) |>
      MI.bindings |> List.split in

  (* Give choice IDs to each conjunctions inside DNF. At the same time, filter
     the inserted tautologies 0=0 during the process. *)
  let laDnfs = List.map (mapi (fun i x -> (i,
    List.filter (fun x -> x <> (EQ, M.empty)) x))) laDnfs in

  List.map (fun assigns ->
    (* Give IDs and flatten. *)
    let dnfChoice, exprs = listFold2 (fun (s, t) x (z, y) ->
      (MI.add x z s), ((List.map (fun z -> (x, z)) y) @ t))
      (MI.empty, []) laIds assigns in

    (* Build the coefficient mapping for all assigned expressions and check
       the operator of each expression. *)
    let coefs, constr, ops, exprGroup =
      List.fold_left (fun (coefs, constr, ops, exprGroup) (gid, (op, coef)) ->
        let exprId = "p" ^ (string_of_int (new_id ())) in

        (* DEBUG: *)
        print_endline ((string_of_int gid) ^ "\t" ^ exprId ^ "\t" ^
          (printExpr (op, coef)));

        (* Building an coefficient mapping in terms of variables *)
        (M.fold (fun k v -> M.addDefault
          M.empty (fun m (k, v) -> M.add k v m) k (exprId, v)) coef coefs),

        (* If the expression is an inequality, its weight should be
           positive *)
        (match op with
          | EQ -> constr
          | LTE -> Expr(GTE, M.add exprId 1 M.empty) :: constr
          | _ -> assert false),

        (* The flag to note that the interpolant should be LTE or EQ *)
        (if op = LTE then M.add exprId op ops else ops),

        (* Correspondance between expression ID and groupID *)
        (M.add exprId gid exprGroup)
      ) (M.empty, [], M.empty, M.empty) exprs in

    let predSols = MI.map (fun (params, a) ->
      (* Parameters have internal names at this moment, so they are renamed
         to 'a' - 'z' by alphabetical order. Make a renaming map and then
         apply it. We beleive there are no more than 26 parameters... *)
      let (i, renameMap) = List.fold_left (fun (i, m) x -> (i + 1),
        M.add x (String.make 1 (Char.chr (97 + i))) m) (0, M.empty) params in
      assert (i <= 26);
      let renameMap = ref renameMap in

      (* Parameter list for the predicate are renamed. *)
      renameList renameMap params,

      (* Predicate body are built from coefficient mapping by extracting only
         relating coefficinet and weight. Finally the body is renamed. *)
      renameExpr renameMap (ops, coefs |>
          M.filter (fun k _ -> List.mem k params || k = "") |>
          M.map (M.filter (fun k _ -> List.mem (M.find k exprGroup) a)))
    ) predMap in

    dnfChoice,
    predSols,
    And(M.fold (fun k v -> (@) [ Expr((if k = "" then
        (* TODO: Consider completeness of Farkas' Lemma application. *)
        (if constr = [] then NEQ else GT) else EQ), v) ]) coefs constr)
  ) (directProduct laDnfs) |>

  (fun x -> x, (MI.map snd predMap), predCopies) |>

  merge

let preprocLefthand =
  List.fold_left (fun (pvars, la) -> function
    | LinearExpr x -> pvars, Some (match la with
        | None -> x
        | Some y -> x &&& y)
    | PredVar pvar -> (pvar :: pvars), la) ([], None)

module Pexpr = struct
  type t = pexpr
  let compare = compare
end
module MP = Merge.Merger(Pexpr)

module PexprList = struct
  type t = pexpr list
  let compare = compare
end
module MPL = Merge.Merger(PexprList)


let combinationCheck lookup f a b c d e =
  let rec choose f a ((bi, bl) as b) c ((di, dl) as d) e = function
    | (i,x)::rest ->
      (choose f a (i, x::bl) c d e rest) &&
      (choose f a b c (i, x::dl) e rest)
    | [] ->
      (bi * di < 0) || (
      List.sort (fun (x,_) (y,_) -> x-y) ([b;d] @ c) |>
      List.split |> (fun (_,x) -> f (a @ x @ e))) in
  let b' = List.map (fun x -> lookup x, x) b in
  let c' = List.map (fun x -> (List.hd x |> lookup), x) c in
  choose f a (-1, []) c' (-1, d) e (List.rev b')

let pexprMerge lookup input origin _ a b c d e =
  if not (combinationCheck lookup (
    fun x -> MP.M.mem x input) a b c d e) then None else

  let ret = MP.M.find origin input &&&
    generatePexprMergeConstr (List.hd b) (List.hd d) in

  (* Test wether the constraint is satisfiable or not. *)
  match Z3interface.integer_programming ret with
    | Some _ -> Some ret
    | None -> None

let pexprListMerge lookup input origin _ a b c d e =
  if not (combinationCheck lookup (
    fun x -> MPL.M.mem x input) a b c d e) then None else

  let b, d = List.hd b, List.hd d in
  match List.fold_left (fun l x ->
    let ret =
      MP.merge_twoLists x pexprMerge b d |>
      MP.M.bindings |>
      List.split |> snd in
    ret @ l) [] (MPL.M.find origin input) with
    | [] -> None
    | x -> Some x

let tryMerge predMerge solution =
  List.fold_left (fun (fail, (preds, constr as sol)) (p1, p2) ->
    if fail then (true, sol) else (

    (* Specified predicate variables must exist. *)
    let [(param1, nf1);(param2, nf2)] = List.map (fun p ->
      assert (M.mem p preds); M.find p preds) [p1;p2] in

    (* Parameters for the predicate variable must match. It should have been
       renamed to (a,b, ...) during the solving algorithm, thus here the
       significance is in the number of the parameters. *)
    assert (param1 = param2);

    (* Try to merge nf1 and nf2. Randomly choose the first constraint if
       succeeds. *)
    let ret = MPL.merge_twoLists [constr] pexprListMerge nf1 nf2 in
    if MPL.M.cardinal ret > 0 then
      (false, (preds, List.hd (snd (MPL.M.choose ret))))
    else
      (true, sol))
  ) (false, solution) predMerge |> snd

let solve (clauses, predMerge) =
  List.map (fun (lh, rh) -> (preprocLefthand lh), rh) clauses |>
  buildGraph |>

  (* DEBUG: Show the constructed graph. *)
  (fun g ->
    let cycle = Traverser.has_cycle g in
    print_endline ("Cycle: " ^ (string_of_bool cycle));
    display_with_gv (Operator.mirror g);
    assert (not cycle);
    g) |>

  flattenGraph |>
  List.map solveTree |>

  reduce (fun (m1, c1) (m2, c2) ->
    (M.merge (fun _ a b ->
      match a, b with
        | None, None
        | Some _, Some _ -> assert false
        | x, None
        | None, x -> x) m1 m2),
    c1 &&& c2) |>

  tryMerge predMerge
