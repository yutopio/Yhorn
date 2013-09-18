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

let of_expr vm (op, coef) =
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
              if M.mem k !vm then
                Variable (M.find k !vm)
              else
                let id = M.cardinal !vm in
                vm := M.add k id !vm;
                Variable id in
            if v = 1 then var
            else Times (int v, var)) :: l) x [] in
      if l = [] then intc 0
      else List.reduce (fun a b -> Plus (a, b)) l) [c1; ~--c2] in

    (* Connect two terms with a relation symbol. *)
    match op with
    | EQ -> Equal (t1, t2)
    | NEQ -> failwith not_polyhedron
    | LT -> Less_Than (t1, t2)
    | LTE -> Less_Or_Equal (t1, t2)
    | GT -> Greater_Than (t1, t2)
    | GTE -> Greater_Or_Equal (t1, t2)

let rec term_of vmi =
  let f t1 g t2 = g (term_of vmi t1) (term_of vmi t2) in
  function
  | Variable id -> M.add (MI.find id vmi) 1 M.empty
  | Coefficient c -> M.add Id.const (Z.to_int c) M.empty
  | Plus (t1, t2) -> f t1 (++) t2
  | Minus (t1, t2) -> f t1 (--) t2
  | Unary_Plus t -> term_of vmi t
  | Unary_Minus t ->  ~-- (term_of vmi t)
  | Times (c, v) -> M.map (fun x -> (Z.to_int c) * x) (term_of vmi v)

let expr_of vmi =
  let f t1 t2 = (term_of vmi t1) -- (term_of vmi t2) in
  function
  | Equal (t1, t2) -> EQ, f t1 t2
  | Less_Than (t1, t2) -> LT, f t1 t2
  | Less_Or_Equal (t1, t2) -> LTE, f t1 t2
  | Greater_Than (t1, t2) -> GT, f t1 t2
  | Greater_Or_Equal (t1, t2) -> GTE, f t1 t2

let integer_qelim vars la =
  let vars = S.diff (fvs la) vars in
  let la = Formula.normalize la in
  let vm = ref M.empty in
  let constrs =
    match la with
    | And x ->
      List.map (
        function
        | Term x -> of_expr vm x
        | _ -> failwith not_polyhedron) x
    | Or x -> failwith not_polyhedron
    | Term x -> [of_expr vm x] in
  let vm = !vm in

  let poly = ppl_new_C_Polyhedron_from_constraints constrs in
  let dim = S.fold (fun x l -> (M.find x vm) :: l) vars [] in
  ppl_Polyhedron_remove_space_dimensions poly dim;
  let constrs = ppl_Polyhedron_get_constraints poly in
  let vmi = M.fold (fun k v m -> MI.add v k m) vm MI.empty in
  And (List.map (fun x -> Term (expr_of vmi x)) constrs)
