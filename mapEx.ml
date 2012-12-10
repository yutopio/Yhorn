open Util

module type S = sig
  include Map.S

  val findDefault: key -> 'a -> 'a t -> 'a
  val addDefault: 'a -> ('a -> 'b -> 'a) -> key -> 'b -> 'a t -> 'a t
  val simpleMerge: 'a t -> 'a t -> 'a t
end

module Make(Ord: Map.OrderedType) = struct
  include Map.Make(Ord)

  let findDefault k d m =
    if mem k m then find k m else d

  (** [addDefault d (+) k v m] adds value v to the existing record value with
      key k in the given mapping m. Adding is done by (+) function given. If no
      binding with key k is present, it will be newly created with the default
      value d. *)
  let addDefault d (+) k v m =
    add k ((+) (findDefault k d m) v) m

  (** [simpleMerge a b] merges two maps with distinct keys. If both maps have
      bindings from the same key, a binding from [a] is considered. *)
  let simpleMerge a = merge (fun _ a b -> tryPick id [a;b]) a
end
