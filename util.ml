let id x = x

(* DEBUG: Copied from util.ml in VHorn ****************************************)

(** compose operator *)
let (-|) f g x = f (g x)
let (-||) f g x y = f (g x y)

(** reverse compose operator *)
let (|-) f g x = g (f x)
let (||-) f g x y = g (f x y)

(** pipeline operator *)
let (|>) x f = f x

(******************************************************************************)

let gcd x y =
  let rec gcd x y =
    if y = 0 then x
    else gcd y (x mod y) in
  assert (x <> 0 && y <> 0);
  let x = if x > 0 then x else -x in
  let y = if y > 0 then y else -y in
  if x > y then gcd x y else gcd y x
let lcm x y = x * y / gcd x y

let fold2 fold_left indexer f x a =
  let i = ref (-1) in
  Array.fold_left (fun x -> f x (a.(incr i; !i))) x

let repeat f n k =
  assert (n >= 0);
  let rec repeat f i n k =
    if i < n then
      repeat f (i + 1) n (f i k)
    else k in
  repeat f 0 n k

let comparePair (x1, y1) (x2, y2) =
  match compare x1 x2 with
    | 0 -> compare y1 y2
    | ret -> ret

let maybeAdd f a b =
  match a, b with
  | None, None -> None
  | None, Some x
  | Some x, None -> Some x
  | Some a, Some b -> Some (f a b)

let maybeApply f = function
  | None -> None
  | Some x -> Some (f x)
