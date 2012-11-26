open Util

module Make(Ord: Map.OrderedType) = struct
  include Map.Make(Ord)

  let findDefault k d m =
    if mem k m then find k m else d

  (** [addDefault k v d (+) m] adds value v to the existing record value with
      key k in the given mapping m. Adding is done by (+) function given. If no
      binding with key k is present, it will be newly created with the default
      value d. *)
  let addDefault k v d (+) m =
    add k ((+) (findDefault k d m) v) m

  (** [simpleMerge a b] merges two maps with distinct keys. If both maps have
      bindings from the same key, a binding from [a] is considered. *)
  let simpleMerge a = merge (fun _ a b -> tryPick id [a;b]) a
end
