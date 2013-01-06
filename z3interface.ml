open Types
open Util
open Z3

(* Calling `preload` will trigger callback registration *)
let _ = preload ()

let timeout = 5000 (* milliseconds *)
let ctx = mk_context [ ]
let _int = mk_int_sort ctx
let _bool = mk_bool_sort ctx

let rec splitVars ret x =
  let (name, rest) =
    try
      let i = String.index x '*' in
      let name = String.sub x 0 i in
      let rest = String.sub x (i + 1) (String.length x - i - 1) in
      (name, Some rest)
    with Not_found -> (x, None) in
  let ret = (mk_const ctx (mk_string_symbol ctx name) _int) :: ret in
  match rest with
    | Some x -> splitVars ret x
    | None -> ret

let rec convert = function
  | Expr (op, coef) -> (
    let (l, r) = M.fold (fun k v (l, r) ->
      if v = 0 then (l, r)
      else
        let l, r = (ref l), (ref r) in
        let t, vp = if v > 0 then l, v else r, (-v) in
        let v = mk_int ctx vp _int in
        let _ =
          if k = "" then t := v :: !t
          else
            match vp, (splitVars [] k) with
              | 1, [k] -> t := k :: !t
              | 1, k -> t := (mk_mul ctx (Array.of_list k)) :: !t
              | _, k -> t := (mk_mul ctx (Array.of_list (v::k))) :: !t in
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

let check ast =
  let s = mk_solver ctx in
  let params = mk_params ctx in
  params_set_uint ctx params (mk_string_symbol ctx ":timeout") timeout;
  solver_set_params ctx s params;
  solver_assert ctx s ast;
  s, solver_check ctx s

(* DEBUG: Show the assertion AST for Z3 before passing to solver.
let check ast =
  print_endline ("Z3 AST: " ^ ast_to_string ctx ast);
  check ast *)

let integer_programming constrs =
  try
    match check (convert constrs) with
      | s, L_TRUE ->
        let md = solver_get_model ctx s in
        let mdn = model_get_num_consts ctx md in
        let m = repeat (fun i m ->
          let fd = model_get_const_decl ctx md i in
          let name = get_symbol_string ctx (get_decl_name ctx fd) in
          match model_get_const_interp ctx md fd with
            | Some ast ->
              let ok, value = get_numeral_int ctx ast in
              M.add name value m
            | None -> m) mdn M.empty in
        Some m
      | _, L_FALSE -> None (* unsatisfiable *)
      | s, L_UNDEF -> (* timeout? *)
        print_endline ("Z3 returned L_UNDEF: " ^
                          (solver_get_reason_unknown ctx s));
        None
  with Error (c, e) ->
    print_string "Z3 Error: ";
    print_endline (try get_error_msg c e with _ -> "unknown");
    None

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
        M.fold (fun k v l -> (k ^ "=" ^ (string_of_int v))::l) sol [])) ^ "]\n")
    | None ->
      print_endline ("Z3 solution: Unsatisfiable"));
  ret
*)

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
    match check ast with
      | _, L_FALSE -> true
      | _ -> false
  with Error (c, e) ->
    print_string "Z3 Error: ";
    print_endline (try get_error_msg c e with _ -> "unknown");
    false
