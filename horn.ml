open Error
open Expr
open Formula
open ListEx
open MapEx
open MTypes
open Types
open Util

let bot = Term (LTE, M.add Id.const 1 M.empty)

let createRename = List.fold_left2 (fun m k v -> M.add k v m) M.empty

let assignParameters assign =
  M.map (fun v -> M.fold (fun k v -> (+) ((M.findDefault 1 k assign) * v)) v 0)

let simplifyCNF clauses =
  let simplifyDF =
    List.fold_left (fun (tautology, exprs) (op, coef as expr) ->
      if tautology then true, []
      else if M.cardinal coef = 0 then
        match op with
        | EQ | LTE | GTE -> true, []
        | NEQ | LT | GT -> false, exprs
      else if M.cardinal coef > 1 || not (M.mem Id.const coef) then
        false, expr :: exprs
      else (
        let c = M.find Id.const coef in
        match op with
        | EQ -> c = 0
        | LTE -> c <= 0
        | GTE -> c >= 0
        | NEQ -> c <> 0
        | LT -> c < 0
        | GT -> c > 0), exprs
    ) (false, []) in

  let contradiction, ret =
    List.fold_left (fun (contradiction, clauses) clause ->
      let tautology, exprs = simplifyDF clause in
      if tautology then contradiction, clauses
      else if contradiction || List.length exprs = 0 then true, []
      else false, (List.sort_distinct Expr.comp exprs) :: clauses
    ) (false, []) clauses in

  contradiction, List.sort_distinct (List.compare Expr.comp) ret

let preprocLefthand =
  Nf.dnf_of_formula |-
  List.map (fun x ->
    let pvars, la =
      List.fold_left (fun (pvars, la) ->
        function
        | LinearExpr x -> pvars, Some (
          let x = normalizeOperator x in
          match la with
          | None -> x
          | Some y -> x &&& y)
        | PredVar pvar -> (pvar :: pvars), la) ([], None) x in

    match la with
    | None -> [pvars, None]
    | Some la ->
      Nf.dnf_of_formula la |>
      List.map (fun x -> pvars, Some (And (List.map (fun x -> Term x) x)))) |-
  List.flatten

let root = G.V.create VBot
module MV = Map.Make(G.V)

let buildGraph clauses =
  (* Create predicate symbol vertices in advance. *)
  let addVp rh_flag (ps, vps) (p, l) =
    let ll = List.length l in
    if rh_flag && ll <> List.length (List.distinct l) then
      (* The parameter definition has the same name variable in the list.
         e.g. x=0->A(x,x). is illegal. *)
      failwith illegal_binder
    else if M.mem p ps then
      (* A predicate symbol which is implied in multiple Horn clauses should
         have the same arity across them. *)
      let (binder, _) = M.find p ps in
      if ll <> List.length binder then
        failwith (invalid_arity p)
      else (ps, vps)
    else
      (* Generate a fresh binder for predicate variable and its template. *)
      let binder, pcoef =
        repeat (fun _ (binder, pcoef) ->
          let v = Id.create () in
          (v :: binder), (M.add v (Id.create ()) pcoef)) ll ([], M.empty) in
      let binder = List.rev binder in
      let pcoef = M.add Id.const (Id.create ()) pcoef in

      (* Create a new predicate vertex and remember it. *)
      let vp = G.V.create VPred in
      let ps = M.add p (binder, Term vp) ps in
      let vps = MV.add vp (p, pcoef) vps in
      (ps, vps) in

  (* Create vertices. *)
  let seed = M.empty, MV.empty in
  let ps, vps =
    List.fold_left (fun x (lh, rh) ->
      let x =
        match rh with
        | PredVar pvar -> addVp true x pvar
        | _ -> x in
      Formula.fold (fun x ->
        function
        | LinearExpr _ -> x
        | PredVar p -> addVp false x p) x lh) seed clauses in
  let preds = M.keys ps in

  let (cs_p, cs_l) =
    List.map (fun (lh, rh) ->
      List.map (fun lh -> lh, rh) (preprocLefthand lh)) clauses |>
    (* TODO: Optimize starting here... *)
    List.flatten |>
    List.partition (fun (_, rh) ->
      match rh with
      | PredVar _ -> true
      | LinearExpr _ -> false) in

  (* Eliminate right-hand linear formula to contradiction. *)
  let cs_l =
    List.fold_left (fun ret ((pvars, la), LinearExpr e) ->
      normalizeOperator e |>
      Nf.cnf_of_formula |>
      simplifyCNF |>
      (function
      | true, _ -> [la]
      | false, exprs ->
        List.map (
          function
          | [] -> assert false
          | l ->
            let neg =
              match List.map (fun x -> Term (negateExpr x)) l with
              | [x] -> x
              | x -> And x in
            maybeAdd (&&&) la (Some neg)) exprs) |>
      List.map (fun la -> (pvars, la), LinearExpr bot) |>
      (@) ret) [] cs_l in
  let clauses = cs_p @ cs_l in
  (* TODO: Optimize ending here... *)

  (* Add implication relations on the Horn graph. *)
  let g =
    List.fold_left (fun g ((pvars, la) as lh, rh) ->
      let (pvars, la), src =
        match rh with
        | PredVar (p, binder) ->
          let (binder', Term src) = M.find p ps in
          let rename = ref (createRename binder binder') in
          ((List.map (fun (p, args) -> p, renameList rename args) pvars),
           (maybeApply (Formula.map (renameExpr rename)) la)), src
        | LinearExpr _ -> lh, root in

      let arrow = G.V.create Arrow in
      let g = G.add_edge_e g (G.E.create src None arrow) in

      let dsts = List.fold_left (fun dsts (p, args) ->
        (* Get the predicate variable vertex and its binder. We will
           relate this vertex from newly-created predicate variable
           vertices that corrensponds to the application of such
           predicates. The edge will carry binding information. *)
        let (binder, Term dst) = M.find p ps in
        let rename = createRename binder args in

        (* Add a edge between origin *)
        (dst, Some rename) :: dsts
      ) [] pvars in

      (* If a linear expression exists on the left-hand, create a
         corresponding vertex. *)
      let dsts =
        match la with
        | None -> dsts
        | Some x ->
          let dst = VLinear (Formula.map normalizeExpr x) in
          (G.V.create dst, None) :: dsts in

      (* Add edges between all left-hand terms and right-hand term. *)
      List.fold_left (fun g (dst, label) ->
        G.add_edge_e g (G.E.create arrow label dst)) g dsts
    ) G.empty clauses in

  (* If a predicate variable does not have any assumption or any implication,
     assume Horn clause bot->P or P/\bot->bot exists. *)
  let vlbot = G.V.create (VLinear bot) in
  let g =
    MV.fold (fun v (p, _) g ->
      let g =
        if G.in_degree g v = 0 then
          let binder, Term v' = M.find p ps in assert (v = v');
          let arity = List.length binder in

          (* Dummy renaming is required. *)
          let dummy = repeat (fun _ k -> (Id.create ()) :: k) arity [] in
          let rename = Some (createRename binder dummy) in

          (* Add P/\bot->bot to the graph. *)
          let arrow = G.V.create Arrow in
          let g = G.add_edge g root arrow in
          let g = G.add_edge g arrow vlbot in
          let g = G.add_edge_e g (G.E.create arrow rename v) in g
        else g in
      let g =
        if G.out_degree g v = 0 then
          (* Add bot->P to the graph. *)
          let bot = G.V.create (VLinear bot) in
          let arrow = G.V.create Arrow in
          let g = G.add_edge g v arrow in
          let g = G.add_edge g arrow vlbot in g
        else g in
      g) vps g in

  (* Return the graph, pred information, and their vertices. *)
  g, ps, vps

type constrTypes =
| LaWeight
| Coef of (Id.t * G.E.t) list
| Simplified of G.V.t

let rec solveGraph (g, ps, vps) visited =
  (* DEBUG: *)
  if !Flags.enable_gv then (
    Types.Display.highlight_vertices := visited;
    display_with_gv (Operator.mirror g)
  );

  let addPcoef e =
    let add (es, m) (k, v) =
      (match e with None -> es | Some e -> e :: es),
      M.addDefault 0 (+) k v m in
    M.addDefault ([], M.empty) add in

  let addLinear (m, pis) coef =
    (* Add to the variable maps for applying Farkas' Lemma. *)
    let pi = Id.create () in

    (* Building an coefficient mapping in terms of variables. *)
    (M.fold (fun k v -> addPcoef None k (pi, v)) coef m), pi :: pis in

  let rec gen_constr ret v =
    if MV.mem v ret then
      (* If the vertex is already registered in the template list,
         simply return it. *)
      ret
    else
      let ret = G.fold_succ_e (fun e ret ->
        let arrow = G.E.dst e in
        let ret, constrs, (m, pis) =
          G.fold_succ_e (fun e (ret, constrs, (m, pis as m_pis)) ->
            let u = G.E.dst e in
            match G.E.label e, G.V.label u with
            | None, VLinear ex ->
              (* TODO: Optimization *)
              let [x] = Nf.dnf_of_formula ex in
              assert (pis = []);
              let x = List.map snd x in (* Ignore LTE operator *)
              let m_pis = List.fold_left addLinear m_pis x in

              (* No renaming should occur for linear expressions. *)
              ret, constrs, m_pis

            | Some rename, VPred ->
              let p, pcoef = MV.find u vps in

              (* Traverse the tree for preceding pred vertices. *)
              let ret = gen_constr ret u in

              let constr =
                if SV.mem u visited then
                  (* If the vertex is already traversed under satisfiability,
                     do not rename the rest part of the constraints. *)
                  MV.find u ret
                else
                  (* Rename the free variables in the constraint, and
                     append to the constraint list. *)
                  let rename = M.fold (fun _ v -> M.add v v) pcoef M.empty in
                  let rename = ref rename in
                  let rename = Formula.map (renameExpr rename) in
                  List.map (fun (a, b) -> a, rename b) (MV.find u ret) in
              let constrs = constr @ constrs in

              let rename = ref rename in
              let f k v = addPcoef (Some (v, e)) (renameVar rename k) (v, 1) in

              (* Building an coefficient mapping in terms of variables. *)
              ret, constrs, ((M.fold f pcoef m), pis)

            | _ -> assert false
          ) g arrow (ret, [], (M.empty, [])) in

        let m, la, quants =
          match G.V.label v with
          | VBot -> m, true, []
          | VPred ->
            (* Add the atomic current predicate template for Farkas' target. *)
            let p, pcoef = MV.find v vps in
            let add k v = addPcoef (Some (v, e)) k (v, -1) in
            let m = M.fold add pcoef m in
            m, false, M.values pcoef
	  | _ -> assert false in

        let constrs =
          (* All left-hand linear inequalities must be weighted non-negative. *)
          List.map (fun pi ->
            (LaWeight, Term (GTE, M.add pi 1 M.empty))) pis |>

          (* Additionally, add constraints to make totals on every
             coefficients zero. *)
          M.fold (fun k (edges, coefs) c ->
            let op = if k = Id.const then if la then GT else GTE else EQ in
            let constr = Coef edges, Term (op, coefs) in
            constr :: c) m |>

          (* Add constraints from predecessors. *)
          (@) constrs
        in

        MV.add arrow constrs ret
      ) g v ret in

    let constrs = G.fold_succ (fun arrow -> (@) (MV.find arrow ret)) g v [] in

    (* NOTE: Required for quantifier elimination.
    let quants =
      match G.V.label v with
      | VBot -> (* bot *) []
      | VPred -> MV.find v vps |> snd |> M.values
      | _ -> assert false
    in *)

    let constr =
      if SV.mem v visited then
        (* No simplification. *)
        constrs
      else
        (* TODO: Quantifier elimination. Also uncomment the block above.
        let quants = List.fold_left (fun a b -> S.add b a) S.empty quants in
        let constrs =
          And (List.map snd constrs) |>
          AtpInterface.integer_qelim quants in *)
        let constrs = And (List.map snd constrs) in
        [Simplified v, constrs]
    in

    MV.add v constr ret
  in

  let split_tag =
    List.fold_left (fun (constrs, m) (tag, ex) ->
      let name = string_of_int (List.length m) in
      (name, ex) :: constrs,
      (name, tag) :: m) ([], []) in

  let constrs = gen_constr MV.empty root in
  let root_constrs, symbol_map = MV.find root constrs |> split_tag in
  
  try
    let sol = Z3interface.solve root_constrs in

    (* If solved, check whether the visited set contains all node. If not,
       extend the set further. Compute frontier. *)
    let visited' =
      SV.fold (
        G.fold_succ (
          G.fold_succ (fun v s ->
            match G.V.label v with
            | VPred -> SV.add v s  
            | _ -> s) g) g) visited visited in

    if SV.cardinal visited <> SV.cardinal visited' then
      (* Broaden non-simplification vertices. *)
      solveGraph (g, ps, vps) visited'
    else
      (* Finished all traversal. *)
      assert false

  with Z3interface.Unsatisfiable uc ->
    (* Restore constraint information. *)
    let uc_tags = List.map (fun x -> List.assoc x symbol_map) uc in

    (* Sort the unsat core tags. *)
    let m, s =
      List.fold_left (fun (m, s) ->
        function
        | Coef es ->
          List.fold_left (fun m (id, es) -> M.add_append id es m) m es, s
        | Simplified v -> m, SV.add v s
        | _ -> m, s) (M.empty, SV.empty) uc_tags in

    (* A routine to find edges, which share the same vertex under the same
       variable. *)
    let findMerge f es =
      let mv =
        List.fold_left (fun m e -> MV.add_append (f e) e m) MV.empty es |>
        MV.filter (fun _ v -> List.length v >= 2) in
      if MV.cardinal mv > 0 then Some (MV.choose mv |> snd) else None in

    (* Find conjunctive unsat information. *)
    let search =
      M.fold (fun _ es ret ->
        (* If already have found split point, continue. *)
        match ret with
        | `Conj _ | `Disj _ -> ret
        | `Unknown ->

        (* Find conjunctive merge. *)
        match findMerge G.E.dst es with
        | Some x -> `Conj x
        | None ->

        (* or, find disjunctive merge. *)
        match findMerge G.E.src es with
        | Some x -> `Disj x
        | None -> `Unknown
      ) m `Unknown in

    match search with
    | `Conj x ->
      split_vertex_conj (g, ps, vps) x
    | `Disj x ->
      split_vertex_disj (g, ps, vps) x
    | `Unknown ->
      (* Extend the graph by LaWeight set s. *)
      solveGraph (g, ps, vps) (SV.union visited s)

and split_vertex (vp, (vps, vp's)) =
  (* Create a new vertex. *)
  let vp' = G.V.create VPred in
  let vp's' = vp' :: vp's in

  (* Create a fresh parameterized template for new predicate vertex. *)
  let (p, pcoef) = MV.find vp vps in
  let pcoef' = M.map (fun _ -> Id.create ()) pcoef in
  let vps' = MV.add vp' (p, pcoef') vps in

  vp', (vps', vp's')

and split_vertex_conj (g, ps, vps) x =
  (* Split DAG. *)

  (* TODO: Optimize the way of splitting by using Coloring problem. *)
  let vp = G.E.dst (List.hd x) in
  let copies = List.tl x in

  let g, (vps, vp's) =
    List.fold_left (fun (g', x) e ->
      let vp', x' = split_vertex (vp, x) in

      let g'= G.remove_edge_e g' e in
      let src = G.E.src e in
      let lbl = G.E.label e in
      let g' = G.add_edge_e g' (G.E.create src lbl vp') in

      let g' =
        G.fold_succ (fun arrow g' ->
          let arrow' = G.V.create Arrow in
          let g' =
            G.fold_succ_e (fun e g' ->
              let dst = G.E.dst e in
              let lbl = G.E.label e in
              G.add_edge_e g' (G.E.create arrow' lbl dst)
            ) g arrow g' in
          G.add_edge g' vp' arrow'
        ) g vp g' in

      g', x'
    ) (g, (vps, [])) copies in

  let p, _ = MV.find vp vps in
  let (binder, vpf) = M.find p ps in
  let vpf =
    Formula.transform (fun x ->
      if x = vp then And (List.map (fun x -> Term x) vp's) else Term x) vpf in
  let ps = M.add p (binder, vpf) ps in

  (* Retry. *)
  (* TODO: Rebuild visited node information; not from scratch. *)
  solveGraph (g, ps, vps) (SV.add root SV.empty)

and split_vertex_disj (g, ps, vps) x =
  (* Split disjunction. *)

  (* TODO: Optimize the way of splitting by using Coloring problem. *)
  let vp = G.E.src (List.hd x) in
  let copies = List.tl x in

  (* Create new pred vertices for disjunction. *)
  let g, (vps, vp's) =
    List.fold_left (fun (g', x) e ->
      let vp', x' = split_vertex (vp, x) in

      let g'= G.remove_edge_e g' e in
      let dst = G.E.dst e in
      let g' = G.add_edge g' vp' dst in
      g', x
    ) (g, (vps, [])) copies in

  (* Temporarily remove edges to the current pred vertices, and group them by
     originating arrows. *)
  let g', mv = G.fold_pred_e (fun e (g', mv) ->
    let src = G.E.src e in
    let lbl = G.E.label e in

    let g' = G.remove_edge_e g' e in
    let mv' = MV.add_append src lbl mv in
    g', mv'
  ) g vp (g, MV.empty) in

  let g', mv = MV.fold (fun arrow lbls (g', mv) ->
    let up = G.pred g' arrow |> List.hd in
    let succ = G.succ_e g' arrow in
    G.remove_vertex g' arrow,
    MV.add arrow (up, succ, lbls) mv
  ) mv (g', MV.empty) in

  let vp's = vp :: vp's in
  let g' =
    MV.fold (fun _ (up, succ, lbls) g ->
      repeat (fun _ l -> vp's :: l) (List.length lbls) [] |>
      List.fold_left (fun g choice ->
        let arrow = G.V.create Arrow in
        let g =
          List.fold_left (fun g e ->
            let lbl = G.E.label e in
            let dst = G.E.dst e in
            G.add_edge_e g (G.E.create arrow lbl dst)
          ) g succ in
        let g =
          List.fold_left2 (fun g lbl dst ->
            G.add_edge_e g (G.E.create arrow lbl dst)
          ) g lbls choice in
        G.add_edge g up arrow
      ) g
    ) mv g' in

  let p, _ = MV.find vp vps in
  let (binder, vpf) = M.find p ps in
  let vpf =
    Formula.transform (fun x ->
      if x = vp then Or (List.map (fun x -> Term x) vp's) else Term x) vpf in
  let ps = M.add p (binder, vpf) ps in

  (* Retry. *)
  (* TODO: Rebuild visited node information; not from scratch. *)
  solveGraph (g, ps, vps) (SV.add root SV.empty)

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
  List.fold_left (fun (clauses, pm) clause ->
    let exec f (lh, rh) =
      let lh' = Formula.map f lh in
      let rh' = f rh in
      lh', rh' in

    let vm = ref M.empty in
    let pm = ref pm in
    let f = function
      | PredVar (p, l) ->
        let def = Id.from_string ("P" ^ string_of_int (M.cardinal !pm)) in
        let p' = M.findDefault def p !pm in
        pm := M.add p p' !pm;
        ignore(renameList vm l);
        PredVar (p', l)
      | LinearExpr e ->
        ignore(Formula.map (renameExpr vm) e);
        LinearExpr e in
    let clause = exec f clause in

    let i = ref 0 in
    let new_name _ = Id.from_string ("x" ^ string_of_int (incr i; !i)) in
    vm := M.map new_name !vm;

    let clause = exec (renameHornTerm vm) clause in
    clause :: clauses, !pm
  ) ([], M.empty)

let solve clauses =
  assert (List.length clauses > 0);

  print_endline ("Yhorn (" ^ Version.date ^ ")\n");
  print_newline ();

  let clauses, pm =
    if !Flags.rename_input then renameClauses clauses
    else clauses, M.empty in
  let pm = M.fold (fun k v -> M.add v k) pm M.empty in

  print_endline (String.concat "\n" (List.map printHorn clauses));
  print_newline ();

  (* Generate the problem graph. *)
  let g, _, _ as problem = buildGraph clauses in

  (* We don't handle cyclic graphs. *)
  assert (not (Traverser.has_cycle g));

  let visited = SV.add root SV.empty in
  let params, exprs = solveGraph problem visited in
  assert false

(*
  (* Create basic template for solution. *)
  let sol_templ = List.fold_left (fun m k -> M.add k (Term k) m) M.empty preds in

  (* Generate constraints for solving the graph. *)
  let params, exprs = solveGraph (g, root) sol_templ in
  let sol = M.merge (fun _ (Some param) (Some exprs) ->
      Some (param, (And (List.map (fun x -> Term x) exprs)))) params exprs in

  (* Rename back to original predicate variable names and simplify. *)
  let sol =
    M.fold (fun k -> M.add (M.findDefault k k pm)) sol M.empty |>
    M.map (fun (p, f) -> p,
      let (contradiction, cnf) = Nf.cnf_of_formula f |> simplifyCNF in
      if contradiction then Term (NEQ, M.empty)
      else Nf.cnf_to_formula cnf)
  in

  (* DEBUG: Solution verification. *)
  List.iter (fun x ->
    print_endline (printHorn x);
    if not (Z3interface.check_clause sol x) then
      failwith incorrect) clauses;

  sol
*)
