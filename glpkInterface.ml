open Error
open Expr
open Formula
open Glpk
open MTypes
open Util

exception No_solution

let eps = 1e-5 (* epsilon *)

let solve constrs =
  let exprs = List.fold_left (fun exprs (_, la) ->
    (match Formula.normalize la with
    | And x ->
      List.map (
        function
        | Term x -> x
        | _ -> failwith disjunctive_constr) x
    | Or x -> failwith disjunctive_constr
    | Term x -> [x]) @ exprs) [] constrs in
  let len_exprs = List.length exprs in

  let pbounds = Array.create len_exprs (0., 0.) in
  let vm, _, constrs = List.fold_left (
    fun (vm, i, constrs) (op, coef) ->
      let c = -. (M.findDefault 0 Id.const coef |> float_of_int) in
      pbounds.(i) <- (
        match op with
        | EQ -> (c, c)
        | NEQ -> failwith disjunctive_constr
        | LT -> (-.infinity, c -. eps)
        | LTE -> (-.infinity, c)
        | GT -> (c +. eps, infinity)
        | GTE -> (c, infinity));

      let vm, constrs = M.fold (fun k v (vm, coef) ->
        if k = Id.const then (vm, constrs)
        else
          let j, vm =
            if M.mem k vm then
              M.find k vm, vm
            else
              let card = M.cardinal vm in
              card, M.add k card vm in
          vm, ((i, j), float_of_int v) :: constrs) coef (vm, constrs) in
      vm, (i + 1), constrs)
    (M.empty, 0, []) exprs in

  let xs = M.cardinal vm in
  let zcoefs = Array.create xs 0. in
  let dummy_constrs = Array.make_matrix len_exprs xs 0. in
  let xbounds = Array.create xs (-.infinity, infinity) in
  let lp = make_problem Minimize zcoefs dummy_constrs pbounds xbounds in

  let constrs = Array.of_list constrs in
  set_class lp Mixed_integer_prog;
  repeat (fun i () -> set_col_kind lp i Integer_var) xs ();
  load_sparse_matrix lp constrs;
  set_message_level lp 0;
  scale_problem lp;
  try
    interior lp;

    let prim = get_col_primals lp in
    M.map (fun i -> int_of_float prim.(i)) vm
  with
  | No_primal_feasible_solution
  | No_dual_feasible_solution ->
    raise No_solution
