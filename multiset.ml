open ListEx
open Util

module type OrderedType =
  sig
    type t
    val compare: t -> t -> int
  end

module type S =
  sig
    type elt
    type t
    val empty: t
    val is_empty: t -> bool
    val mem: elt -> t -> bool
    val add: elt -> t -> t
    val singleton: elt -> t
    val remove: elt -> t -> t
    val union: t -> t -> t
    val inter: t -> t -> t
    val diff: t -> t -> t
    val compare: t -> t -> int
    val equal: t -> t -> bool
    val subset: t -> t -> bool
    val iter: (elt -> unit) -> t -> unit
    val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all: (elt -> bool) -> t -> bool
    val exists: (elt -> bool) -> t -> bool
    val filter: (elt -> bool) -> t -> t
    val partition: (elt -> bool) -> t -> t * t
    val cardinal: t -> int
    val elements: t -> elt list
    val min_elt: t -> elt
    val max_elt: t -> elt
    val choose: t -> elt
    val split: elt -> t -> t * int * t
    val unique: t -> t
    val set_multiplicity: elt -> int -> t -> t
    val get_multiplicity: elt -> t -> int
  end

module Make(Ord: OrderedType) =
  struct
    type elt = Ord.t

    module M = Map.Make(Ord)
    type t = int M.t

    let empty = M.empty
    let is_empty = M.is_empty
    let mem x = M.mem

    let add x t =
      try
	let count = M.find x t in
	M.add x (count + 1) t
      with Not_found -> M.add x 1 t

    let singleton x = M.add x 1 M.empty

    let remove x t =
      try
	let count = M.find x t in
	if count = 1 then M.remove x t
	else M.add x (count - 1) t
      with Not_found -> t

    let set_op f s1 s2 =
      List.sorted_multimap Ord.compare
        (fun _ -> f)
        (List.map M.bindings [s1; s2]) |>
      List.fold_left (fun m (k, v) -> M.add k v m) M.empty

    let union =
      set_op (function
        | [(_, x); (_, y)] -> Some (max x y)
        | [_, x] -> Some x
        | _ -> assert false)

    let inter =
      set_op (function
        | [(_, x); (_, y)] -> Some (min x y)
        | [_, x] -> None
        | _ -> assert false)

    let diff =
      set_op (function
        | [(0, x); (1, y)]
        | [(1, y); (0, x)] -> if x > y then Some (x - y) else None
        | [0, x] -> Some x
        | [1, _] -> None
        | _ -> assert false)

    let compare = M.compare compare
    let equal s1 s2 = compare s1 s2 = 0

    exception Stop
    let rec subset s1 s2 =
      try
        List.sorted_multimap Ord.compare
          (fun _ -> function
            | [(0, x); (1, y)]
            | [(1, y); (0, x)] -> if x <= y then None else raise Stop
            | [0, x] -> raise Stop
            | [1, _] -> None
            | _ -> assert false)
          (List.map M.bindings [s1; s2]);
        true
      with Stop -> false

    let iter f = M.iter (fun k v -> repeat (fun _ () -> f k) v ())
    let fold f = M.fold (fun k v -> repeat (fun _ -> f k) v)

    let for_all p =
      M.for_all (fun k ->
        let rec f n =
          if n > 0 then
            if p k then f (n - 1) else false
          else true in
        f)

    let exists p =
      M.exists (fun k ->
        let rec f n =
          if n > 0 then
            if p k then true else f (n - 1)
          else false in
        f)

    let filter p =
      M.mapi (fun k v -> repeat (fun _ x -> if p k then x + 1 else x) v 0) |-
      M.filter (fun _ -> (<) 0)

    let partition p s =
      let s1 = filter p s in
      s1, (diff s s1)

    let cardinal s = M.fold (fun _ -> (+)) s 0

    let elements s =
      M.fold (fun k v -> (@) (repeat (fun _ l -> k :: l) v [])) s [] |>
      List.rev

    let min_elt = M.min_binding |- fst
    let max_elt = M.max_binding |- fst
    let choose = min_elt

    let split x m =
      let (l, data, r) = M.split x m in
      match data with
        | None -> l, 0, r
        | Some x -> l, x, r

    let unique = M.map (fun _ -> 1)

    let get_multiplicity k m =
      try M.find k m
      with Not_found -> 0

    let set_multiplicity k v =
      if v > 0 then M.add k v
      else if v = 0 then M.remove k
      else invalid_arg "Multiplicity cannot be negative."
  end
