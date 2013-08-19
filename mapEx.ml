open ListEx
open Util

module Map = struct

module type S = sig
  include Map.S

  val keys: 'a t -> key list
  val values: 'a t -> 'a list
  val findDefault: 'a -> key -> 'a t -> 'a
  val addDefault: 'a -> ('a -> 'b -> 'a) -> key -> 'b -> 'a t -> 'a t
  val add_append: key -> 'a -> 'a list t -> 'a list t
  val simpleMerge: 'a t -> 'a t -> 'a t
end

module Make(Ord: Map.OrderedType) = struct
  include Map.Make(Ord)

  let keys m = fold (fun k _ l -> k :: l) m []
  let values m = fold (fun _ v l -> v :: l) m []

  let findDefault d k m =
    if mem k m then find k m else d

  (** [addDefault d (+) k v m] adds value v to the existing record value with
      key k in the given mapping m. Adding is done by (+) function given. If no
      binding with key k is present, it will be newly created with the default
      value d. *)
  let addDefault d (+) k v m =
    add k ((+) (findDefault d k m) v) m

  let add_append k elem m = addDefault [] (fun l e -> e :: l) k elem m

  (** [simpleMerge a b] merges two maps with distinct keys. If both maps have
      bindings from the same key, a binding from [a] is considered. *)
  let simpleMerge a = merge (fun _ a b -> List.try_pick id [a;b]) a
end

end
