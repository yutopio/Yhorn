open Formula
open ListEx

type 'a t = 'a list list

let of_formula cnf formulae =
  let rec internal formulae ret =
    match formulae with
    | [] -> List.rev ret
    | x :: l ->
      let ret =
        match x with
        | Term x -> [ x ] :: ret
        | And x | Or x -> (List.direct_product (internal x [])) @ ret
      in
      internal l ret
  in
  match cnf, formulae with
  | true, And x
  | false, Or x -> internal x []
  | _ -> internal [ formulae ] []
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
