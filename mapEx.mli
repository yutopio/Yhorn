module type S = sig
  include Map.S

  val findDefault: key -> 'a -> 'a t -> 'a
  val addDefault: 'a -> ('a -> 'b -> 'a) -> key -> 'b -> 'a t -> 'a t
  val simpleMerge: 'a t -> 'a t -> 'a t
end

module Make (Ord : Map.OrderedType) : S with type key = Ord.t
