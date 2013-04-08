open Util
open Types

let buildGraph clauses =
  (* Create predicate symbol vertices in advance. *)
  let predVertices = List.fold_left (fun predVertices (_, rh) ->
    match rh with
      | PredVar (p, l) ->
        if M.mem p predVertices then
          (* A predicate symbol should not be implied in different Horn clauses.
             e.g. x=0->A(x). y=0->A(y). is illegal. *)
          assert false
        else if List.length l <> List.length (distinct l) then
          (* The parameter definition has the same name variable in the list.
             e.g. x=0->A(x,x). is illegal. *)
          assert false
        else
          (* Create a new predicate vertex and remember it. *)
          M.add p (G.V.create rh) predVertices
      | _ -> predVertices) M.empty clauses in
  let predVertices = ref predVertices in

  List.fold_left (fun g (lh, rh) ->
    let src = match rh with
      | PredVar (p, _) -> M.find p !predVertices
      | LinearExpr _ -> G.V.create rh in
    let g = G.add_vertex g src in

    let (pvars, la) = lh in
    let g, dsts = List.fold_left (fun (g, dsts) (p, args) ->
      (* Get (or create if needed) the predicate variable vertex and its binder.
         We will relate this vertex from newly-created predicate variable
         vertices that corrensponds to the application of such predicates. The
         edge will carry binding information. *)
      let g, dst, binders =
        if M.mem p !predVertices then
          (* If exists, extract binders from the vertex label. *)
          let dst = M.find p !predVertices in
          let PredVar (_, binders) = G.V.label dst in
          g, dst, binders
        else (
          (* If not yet exists, create a new vertex with a fresh binder. [bot]
             implies the predicate symbol. This means that this predicate
             variable has no implication in input Horn clauses. *)
          let binders = repeat (fun _ l -> (Id.create ()) :: l)
            (List.length args) [] in
          let dst = G.V.create (PredVar (p, binders)) in
          let bot = G.V.create (LinearExpr (Expr (EQ, M.add Id.const 1 M.empty))) in
          let g = G.add_edge g dst bot in
          predVertices := M.add p dst !predVertices;
          g, dst, args) in

      (* Build a name mapping between referred predicate variable (appears on
         the right-hand of Horn clause) and referring one (on the left-hand).

         NOTE: You must not omit same-name bindings such as (x,x). Otherwise, it
         will harm renaming during building constraints around line 156-158. *)
      let renames = listFold2 (fun l a b -> (a, b) :: l) [] binders args in

      (* Add a edge between origin *)
      g, (dst, Some renames) :: dsts
    ) (g, []) pvars in

    (* If a linear expression exists on the left-hand, create a corresponding
       vertex. *)
    let dsts = match la with
      | None -> dsts
      | Some x -> (G.V.create (LinearExpr x), None) :: dsts in

    (* Add edges between all left-hand terms and right-hand term. *)
    List.fold_left (fun g (dst, label) ->
      G.add_edge_e g (G.E.create src label dst)) g dsts
  ) G.empty clauses

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
    let predMap = ref M.empty in
    let predCopies = ref M.empty in

    let g, v, nameMap = match G.V.label v with
      | LinearExpr e ->
        let nameMap = ref M.empty in
        ignore(mapFormula (renameExpr nameMap) e);
        g, v, M.fold (fun k v -> M.add k k) !nameMap M.empty
      | PredVar (_, l) ->
        let top = G.V.create (LinearExpr (Expr (EQ, M.empty))) in
        G.add_edge_e g (G.E.create top (Some (
          List.map (fun x -> (x, x)) l)) v), top, M.empty
    in

    let rec f v nameMap g' =
      let registerLa la =
        let key = MI.cardinal !laGroups in
        laGroups := MI.add key la !laGroups; key in

      let (g', u's, u'keys, _) = G.fold_succ_e (fun e
        (g', u's, u'keys, hadLa) ->

        let u = G.E.dst e in
        match G.V.label u, G.E.label e with
          | PredVar _, Some bindings ->
            (* Bindings of predicate variables are converted to linear equations
               so that it can be treated easy. Note that the binder and argument
               will have different names even if they have the same one before
               conversion.*)
            let nameMap = List.fold_left (fun m (x, y) ->
              let y' = renameVar nameMap y in
              M.add x y' m) M.empty bindings in

            (* Traverse children first to unify predicate variable nodes. *)
            let (g', u', u'keys') = f u (ref nameMap) g' in
            g', ((u', Some bindings) :: u's), u'keys' @ u'keys, hadLa

          | LinearExpr e, None ->
            if hadLa then
              (* NOTE: Linear expressions must appear only once. *)
              assert false
            else
              let laKey = registerLa (e, !nameMap) in
              g', (G'.V.create (La laKey), None) :: u's, laKey :: u'keys, true

          | _ -> assert false
      ) g v (g', [], [], false) in

      let v' = G'.V.create (
        match G.V.label v with
          | PredVar (p, param) ->
            let pid = Id.create () in
            predMap := M.add pid (param, u'keys) !predMap;
            predCopies := M.addDefault [] (fun l x -> x :: l) p pid !predCopies;
            Pid pid

          | LinearExpr e ->
            (* NOTE: The vertex 'v' must be the root of traversal. *)
            La (registerLa (!!!e, !nameMap))) in

      (* Add edges between new left-hand nodes and right-hand node. *)
      let g' = List.fold_left (fun g' (u', lb) ->
        G'.E.create u' lb v' |> G'.add_edge_e g') g' u's in
      g', v', u'keys
    in
    let (g', _, _) = f v (ref nameMap) G'.empty in
    g', !laGroups, !predMap, !predCopies)

let solveTree g =
  (* Assign a template to all predicate variables. *)
  (* TODO: Currently supported template is only [1] in Module Template type.
           Any larger templates should be available in future. *)
  let templ =
    G.fold_vertex (fun v m ->
      match G.V.label v with
      | LinearExpr _ -> m
      | PredVar (p, param) ->
        let rename =
          List.fold_left (fun m x -> M.add x (Id.create ()) m) M.empty param |>
          M.add Id.const (Id.create ()) in
        M.add p (param, rename) m) g M.empty in

  let constrs = G.fold_vertex (fun v x ->
    let l1, l2 = G.fold_succ_e (fun e (l1, l2) ->
      match G.E.label e, G.V.label (G.E.dst e) with
      | None, LinearExpr e ->
        print_endline ("LinE  " ^ printFormula printExpr e);
        e :: l1, l2
      | Some rename, PredVar (p, param) ->
        l1,
        (* TODO: Currently all template are considered to be LTE. *)
        let rename = List.fold_left (fun m (a, b) ->
          M.add a b m) M.empty rename in
        let _, pm = M.find p templ in
        let pm = M.fold (fun k -> M.add (
          if k = Id.const then Id.const
          else M.find k rename)) pm M.empty in
        let pexpr = M.empty, M.map (fun x -> M.add x 1 M.empty) pm in
        (print_endline ("Pred  " ^ printPexpr pexpr);
        pm :: l2)
    ) g v ([], []) in

    if l1 = [] && l2 = [] then x else (

    let addPcoef = M.addDefault M.empty (fun m (k, v) -> M.add k v m) in

    let addLinear x =
      mapFormula normalizeExpr |-
      splitNegation |-
      convertToNF false |-

      (* TODO: Support of disjunctions.
         We now only consider first conjunction in DNF. *)
      (function
      | [x] -> x
      | [] -> assert false
      | x::_ ->
        print_endline "Omitting conjunctions..."; x) |-

      (* Filter the inserted tautologies 0=0 during the process. *)
      List.filter (fun x -> x <> (LTE, M.empty)) |-

      (* Add to the variable maps for applying Farkas' Lemma. *)
      List.fold_left (fun (m, pis) (op, coef) ->
        let pi = Id.create () in

        (* Building an coefficient mapping in terms of variables. *)
        (M.fold (fun k v -> addPcoef k (pi, v)) coef m),

        (* TODO: Linear expression must be normalized to LTE. No EQ allowed. *)
        (match op with
        | LTE -> pi :: pis
        | _ -> assert false)) x in

    let m, pis = List.fold_left addLinear (M.empty, []) l1 in

    let m = List.fold_left (fun m pcoef ->
      (* Building an coefficient mapping in terms of variables. *)
      (M.fold (fun k v -> addPcoef k (v, 1)) pcoef m))
      m l2 in

    let m =
      match G.V.label v with
      | LinearExpr e ->
        addLinear (m, []) (!!! e) |> fst
      | PredVar (p, param) ->
        (* TODO: Currently all template are considered to be LTE. *)
        let _, pcoef = M.find p templ in

        (* Building an coefficient mapping in terms of variables. *)
        M.fold (fun k v -> addPcoef k (v, -1)) pcoef m |>
        addPcoef Id.const (Id.const, 1) in

    (* Every linear inequality must be weighted non-negative. *)
    List.fold_left (fun l pi -> Expr (GTE, M.add pi 1 M.empty) :: l) x pis |>

    (* Additionally, add constraints to make totals on every
       coefficients zero. *)
    M.fold (fun k v c ->
      Expr ((if k = Id.const then GT else EQ), v) :: c) m
    )) g [] in

  M.map (fun (param, v) -> param,
    [[M.fold (fun _ v -> M.add v LTE) v M.empty,
      M.map (fun v -> M.add v 1 M.empty) v]]) templ,
  [ Id.create () ],
  MI.add 1 (And constrs) MI.empty

let simplifyPCNF clauses =
  let simplifyPDF exprs =
    assert (List.length exprs > 0);
    let tautology = List.exists (fun (_, coef) ->
      (* NOTE: We don't need to consider operator because only EQ and LTE are
         used. If there is no coefficient, it must be tautology. *)
      List.length (M.keys coef) = 0) exprs in
    if tautology then []
    else exprs in

  assert (List.length clauses > 0);
  let filtered = List.fold_left (fun l x ->
    let x = simplifyPDF x in
    if x = [] then l else x :: l) [] clauses in
  if List.length filtered = 0 then [[M.empty, M.empty]] (* Tautology *)
  else [M.empty, M.empty] :: filtered

let renameClauses =
  List.fold_left (fun (clauses, pm) (lh, rh) ->
    let vm = ref M.empty in
    let pm = ref pm in
    let f = function
      | PredVar (p, l) ->
        let p' = M.findDefault (Id.from_string (
          "P" ^ string_of_int (M.cardinal !pm))) p !pm in
        pm := M.add p p' !pm;
        ignore(renameList vm l);
        PredVar (p', l)
      | LinearExpr e ->
        ignore(mapFormula (renameExpr vm) e);
        LinearExpr e in
    let terms = List.map f (rh::lh) in
    let i = ref 0 in
    vm := M.map (fun v -> Id.from_string ("x" ^ string_of_int (incr i; !i))) !vm;
    let rh::lh = List.map (renameHornTerm vm) terms in
    (lh, rh) :: clauses, !pm
  ) ([], M.empty)

let solve clauses =
  assert (List.length clauses > 0);

  (* DEBUG: *)
  print_newline ();
  print_endline "Yhorn\n";
  let renClauses, pm = renameClauses clauses in
  let pm = M.fold (fun k v -> M.add v k) pm M.empty in
  print_endline (
    String.concat "\n" (List.map printHorn renClauses) ^ "\n");
  let preprocLefthand = List.fold_left (fun (pvars, la) -> function
    | LinearExpr x -> pvars, Some (match la with
        | None -> x
        | Some y -> x &&& y)
    | PredVar pvar -> (pvar :: pvars), la) ([], None) in
  List.map (fun (lh, rh) -> (preprocLefthand lh), rh) renClauses |>
  buildGraph |>

  (* DEBUG: Show the constructed graph. *)
  (fun g ->
    let cycle = Traverser.has_cycle g in
    print_endline ("Cycle: " ^ (string_of_bool cycle));
    display_with_gv (Operator.mirror g);
    assert (not cycle);
    g) |>

  solveTree |>

  fun (m, i, c) ->
    M.fold (fun k (p, v) -> M.add (M.find k pm) (p, simplifyPCNF v)) m M.empty,
    (i, Puf.create (List.length i), c)

let solve x = x, (solve x)
