open Formula
open ListEx

type 'a t = 'a list list

let of_formula cnf formula =
  let rec internal formula ret =
    match formula with
    | [] -> List.rev ret
    | x :: l ->
      let ret =
        match x with
        | Term x -> [ x ] :: ret
        | And x | Or x -> (List.direct_product (internal x [])) @ ret
      in
      internal l ret
  in
  let formula = normalize formula in
  match cnf, formula with
  | true, And x
  | false, Or x -> internal x []
  | _ -> internal [ formula ] []
let cnf_of_formula x = of_formula true x
let dnf_of_formula x = of_formula false x

let to_formula cnf nf =
  let x =
    List.map (
      fun x ->
        match List.map (fun x -> Term x) x with
        | [] -> assert false
        | [x] -> x
        | x -> if cnf then Or x else And x) nf
  in
  match x with
  | [] -> assert false
  | [x] -> x
  | x -> if cnf then And x else Or x
let cnf_to_formula x = to_formula true x
let dnf_to_formula x = to_formula false x
