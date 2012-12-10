open Util
open Types

module Merger (X: Map.OrderedType) : sig
  module ResultKey : sig
    type t = X.t list list
    val compare : t -> t -> int
  end

  module MR : MapEx.S with type key = ResultKey.t

  val merge_twoLists : 'a ->
    ('a -> X.t list list -> X.t list ->
     X.t list -> 'a option) ->
    X.t list -> X.t list -> 'a MR.t
end
