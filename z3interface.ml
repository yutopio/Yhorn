open Types
open Util
open Z3

(* Calling `preload` will trigger callback registration *)
let _ = preload ()

let ctx = mk_context [ "MODEL", "true" ]
let _int = mk_int_sort ctx
let _bool = mk_bool_sort ctx

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
            let k = mk_const ctx (mk_string_symbol ctx k) _int in
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

let integer_programming constrs =
  let ast = convert constrs in
  let s = mk_solver ctx in
  solver_assert ctx s ast;
  match solver_check ctx s with
    | L_TRUE ->
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
    | L_FALSE -> None (* unsatisfiable *)
    | L_UNDEF -> assert false
