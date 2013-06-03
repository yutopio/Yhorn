open Types
open Util
open Z3

(* Calling `preload` will trigger callback registration *)
let _ = preload ()

let timeout = 5000 (* milliseconds *)
let ctx = mk_context [ "MODEL", "true" ]
let _int = mk_int_sort ctx
let _bool = mk_bool_sort ctx

let show_error (Error (c, e)) =
  print_string "Z3 Error: ";
  print_endline (try get_error_msg c e with _ -> "unknown")

let rec convert = function
  | Expr (op, coef) -> (
    let (l, r) = M.fold (fun k v (l, r) ->
      if v = 0 then (l, r)
      else
        let l, r = (ref l), (ref r) in
        let t, vp = if v > 0 then l, v else r, (-v) in
        let v = mk_int ctx vp _int in
        let _ =
          if k = Id.const then t := v :: !t
          else
            let k = mk_const ctx (
              try mk_string_symbol ctx (Id.string_of k)
              with _ -> mk_int_symbol ctx (Id.int_of k)) _int in
            if vp = 1 then t := k :: !t
            else t := (mk_mul ctx [| k; v |]) :: !t in
        (!l, !r)) coef ([], []) in
    let [ l; r ] = List.map (function
      | [] -> mk_int ctx 0 _int
      | [x] -> x
      | l -> mk_add ctx (Array.of_list l)) [ l; r ] in
    match op with
      | EQ -> mk_eq ctx l r
      | NEQ -> mk_not ctx (mk_eq ctx l r)
      | LT -> mk_lt ctx l r
      | LTE -> mk_le ctx l r
      | GT -> mk_gt ctx l r
      | GTE -> mk_ge ctx l r)
  | And x -> mk_and ctx (Array.of_list (List.map convert x))
  | Or x -> mk_or ctx (Array.of_list (List.map convert x))

let check_ast asts =
  let s = mk_solver ctx in
  let params = mk_params ctx in
  params_set_uint ctx params (mk_string_symbol ctx ":timeout") timeout;
  params_set_bool ctx params (mk_string_symbol ctx "unsat_core") true;
  solver_set_params ctx s params;

  let ast_symbols =
    List.fold_left (fun l x ->
      let name = "ast_" ^ string_of_int (List.length l) in
      let symbol = Z3.mk_string_symbol ctx name in
      let ast = Z3.mk_const ctx symbol _bool in
      Z3.solver_assert ctx s (Z3.mk_iff ctx ast x);
      ast :: l
    ) [] asts in

  s, solver_check_assumptions ctx s (Array.of_list ast_symbols)
let check = function
  | And x -> check_ast (List.map convert x)
  | x -> check_ast [ convert x ]

(* DEBUG: Show the assertion AST for Z3 before passing to solver.
let check ast =
  print_endline ("Z3 AST: " ^ ast_to_string ctx ast);
  check ast *)

let check_formula formula =
  try
    match check formula with
      | _, L_TRUE -> Some true
      | _, L_FALSE -> Some false
      | _, L_UNDEF -> None
  with Error (_, _) as e -> (show_error e; None)

let integer_programming constrs =
  try
    match check constrs with
      | s, L_TRUE ->
        let md = solver_get_model ctx s in
        let mdn = model_get_num_consts ctx md in
        let m = repeat (fun i m ->
          let fd = model_get_const_decl ctx md i in
          let symbol = get_decl_name ctx fd in
          let id = match get_symbol_kind ctx symbol with
            | INT_SYMBOL ->
              Id.from_int (get_symbol_int ctx symbol)
            | STRING_SYMBOL ->
              Id.from_string (get_symbol_string ctx symbol) in
          match model_get_const_interp ctx md fd with
            | Some ast ->
              let ok, value = get_numeral_int ctx ast in
              M.add id value m
            | None -> m) mdn M.empty in
        Some m
      | s, L_FALSE ->
        let unsat_core = solver_get_unsat_core ctx s in
        let size = ast_vector_size ctx unsat_core in
        let str = repeat (fun i k ->
          let ast = ast_vector_get ctx unsat_core i in
          let str = ast_to_string ctx ast in
          k ^ str ^ "\n") size "" in
        failwith (str);
        None (* unsatisfiable *)
      | s, L_UNDEF -> (* timeout? *)
        print_endline ("Z3 returned L_UNDEF: " ^
                          (solver_get_reason_unknown ctx s));
        None
  with Error (_, _) as e -> (show_error e; None)

(* DEBUG:
let integer_programming constr =
  print_endline ("Z3 problem: " ^ (printFormula printExpr constr));
  let _start = Sys.time () in
  let ret = integer_programming constr in
  let _end = Sys.time () in
  print_endline ("Z3 elapsed time: " ^
    (string_of_float (_end -. _start)) ^ " sec.");
  (match ret with
    | Some sol ->
      print_endline ("Z3 solution: [" ^ (String.concat ", " (
        M.fold (fun k v l -> (Id.print k ^ "=" ^ (string_of_int v))::l) sol [])) ^ "]\n")
    | None ->
      print_endline ("Z3 solution: Unsatisfiable\n"));
  ret
*)

let check_interpolant (a, b) i =
  let ast = mk_or ctx [|
    mk_not ctx (mk_implies ctx (convert a) (convert i));
    mk_and ctx [| (convert i); (convert b) |] |] in
  try
    match check_ast [ast] with
      | _, L_FALSE -> true
      | _ -> false
  with e -> (show_error e; false)

let check_clause pred (lh, rh) =
  let rh::lh = List.map (function
    | PredVar (p, args) ->
      let (binder, la) = M.find p pred in
      let renames = listFold2 (fun m a b -> M.add a b m) M.empty binder args in
      mapFormula (renameExpr (ref renames)) la
    | LinearExpr x -> x) (rh::lh) in
  let lh = reduce (&&&) lh in

  let ast = mk_not ctx (mk_implies ctx (convert lh) (convert rh)) in
  try
    match check_ast [ast] with
      | _, L_FALSE -> true
      | _ -> false
  with e -> (show_error e; false)
