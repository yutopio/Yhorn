open Formula
open Error
open Expr
open Gmp
open ListEx
open MTypes
open Ppl_ocaml
open Types
open Util

let int = Z.of_int
let intc x = Coefficient (int x)

let of_expr vl (op, coef) =
  let coef = M.filter (fun _ -> (<>) 0) coef in
  if M.cardinal coef = 0 then
    (* If no term is given, return the Boolean value. *)
    match op with
    | EQ | LTE | GTE -> Equal (intc 0, intc 0)
    | NEQ | LT | GT -> Equal (intc 0, intc 1)
  else
    let c1, c2 = M.partition (fun _ -> (<) 0) coef in

    (* Build terms. *)
    let [t1; t2] = List.map (fun x ->
      let l =
        M.fold (fun k v l -> (
          if k = Id.const then intc v
          else
            let var =
              let i = List.indexof k !vl in
              if i <> -1 then
                Variable i
              else
                let id = List.length !vl in
                vl := !vl @ [k];
                Variable id in
            if v = 1 then var
            else Times (int v, var)) :: l) x [] in
      if l = [] then intc 0
      else List.reduce (fun a b -> Plus (a, b)) l) [c1; ~--c2] in

    (* Connect two terms with a relation symbol. *)
    match op with
    | EQ -> Equal (t1, t2)
    | NEQ -> failwith disjunctive_constr
    | LT -> Less_Than (t1, t2)
    | LTE -> Less_Or_Equal (t1, t2)
    | GT -> Greater_Than (t1, t2)
    | GTE -> Greater_Or_Equal (t1, t2)

let rec term_of vl =
  let f t1 g t2 = g (term_of vl t1) (term_of vl t2) in
  function
  | Variable id -> M.add (List.nth vl id) 1 M.empty
  | Coefficient c -> M.add Id.const (Z.to_int c) M.empty
  | Plus (t1, t2) -> f t1 (++) t2
  | Minus (t1, t2) -> f t1 (--) t2
  | Unary_Plus t -> term_of vl t
  | Unary_Minus t ->  ~-- (term_of vl t)
  | Times (c, v) -> M.map (fun x -> (Z.to_int c) * x) (term_of vl v)

let expr_of vl =
  let f t1 t2 = (term_of vl t1) -- (term_of vl t2) in
  function
  | Equal (t1, t2) -> EQ, f t1 t2
  | Less_Than (t1, t2) -> LT, f t1 t2
  | Less_Or_Equal (t1, t2) -> LTE, f t1 t2
  | Greater_Than (t1, t2) -> GT, f t1 t2
  | Greater_Or_Equal (t1, t2) -> GTE, f t1 t2

let integer_qelim quants la =
  if S.cardinal quants >= !Flags.ppl_quant_threshold then la else (

  let vars = S.diff (fvs la) quants in
  let vars = S.fold (fun x l -> x :: l) vars [] in
  let la = Formula.normalize la in

  let vl = ref [] in
  let constrs =
    match la with
    | And x ->
      List.map (
        function
        | Term x -> of_expr vl x
        | _ -> failwith disjunctive_constr) x
    | Or x -> failwith disjunctive_constr
    | Term x -> [of_expr vl x] in
  let vl = !vl in

  if !Flags.ppl_debug_flag then (
    let str_vars = String.concat "," (List.map Id.print vars) in
    print_endline ("Simplification [" ^ str_vars ^ "]: " ^
                      Formula.print printExpr la));

  let poly = ppl_new_C_Polyhedron_from_constraints constrs in

  (* Eliminate qunatifiers by the specified number of variables in
     every iteration. *)
  let vl =
    if !Flags.ppl_quant_chop <= 0 then (
      List.map (fun x -> List.index_of x vl) vars |>
      ppl_Polyhedron_remove_space_dimensions poly;
      List.partition (fun x -> List.mem x vars) vl |> snd
    ) else
      List.chop !Flags.ppl_quant_chop vars |>
      List.fold_left (fun vl var ->
        List.map (fun x -> List.index_of x vl) var |>
            ppl_Polyhedron_remove_space_dimensions poly;
        List.partition (fun x -> List.mem x var) vl |> snd) vl
  in

  let constrs = ppl_Polyhedron_get_constraints poly in
  let ret = And (List.map (fun x -> Term (expr_of vl x)) constrs) in

  if !Flags.ppl_debug_flag then
    print_endline ("Simplified: " ^ Formula.print printExpr ret);
  ret)
