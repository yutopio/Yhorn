open ListEx

type 'a t =
| Term of 'a
| And of 'a t list
| Or of 'a t list

let rec print printer x =
  let ret =
    match x with
    | Term x -> `A x
    | And x -> `B(x, " & ")
    | Or x -> `B(x, " | ")
  in

  match ret with
  | `A x -> printer x
  | `B(x, y) ->
    String.concat y (List.map (
      fun x -> "(" ^ (print printer x) ^ ")") x)

let combine opAnd x y =
  match (opAnd, x, y) with
  | (true, And x, And y) -> And (y @ x)
  | (true, And x, _) -> And (y :: x)
  | (true, _, And y) -> And (y @ [ x ])
  | (true, _, _) -> And [ y ; x ]
  | (_, Or x, Or y) -> Or (y @ x)
  | (_, Or x, _) -> Or (y :: x)
  | (_, _, Or y) -> Or (y @ [ x ])
  | _ -> Or [ y ; x ]
let (&&&) x = combine true x
let (|||) x = combine false x

let rec map f =
  function
  | And x -> And (List.map (map f) x)
  | Or x -> Or (List.map (map f) x)
  | Term e -> Term (f e)

let rec transform f =
  function
  | And x -> And (List.map (transform f) x)
  | Or x -> Or (List.map (transform f) x)
  | Term x -> f x

let rec flatten =
  function
  | Term (Term x) -> Term x
  | Term (And x) -> And x
  | Term (Or x) -> Or x
  | And x -> And (List.map flatten x)
  | Or x -> Or (List.map flatten x)

let rec fold f seed =
  function
  | And x | Or x -> List.fold_left (fold f) seed x
  | Term e -> f seed e

let count x = fold (fun x _ -> x + 1) 0 x

let normalize =
  function
  | And x -> List.reduce (&&&) x
  | And x -> List.reduce (|||) x
  | x -> x
