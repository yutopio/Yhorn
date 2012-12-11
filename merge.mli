open Util
open Types

module Merger (X: Map.OrderedType) : sig
  module Key : sig
    type t = X.t list list
    val compare : t -> t -> int
  end

  module M : MapEx.S with type key = Key.t

  val merge_twoLists :
    'a ->             (* default value *)
    ((X.t -> int) ->  (* lookup *)
     'a M.t ->        (* intermediate values *)
     X.t list list -> (* original *)
     X.t list list -> (* merged *)
     X.t list list -> (* a *)
     X.t list ->      (* b *)
     X.t list list -> (* c *)
     X.t list ->      (* d *)
     X.t list list -> (* e *)
     'a option) ->    (* merge evaluation *)
    X.t list ->       (* input 1 to merge *)
    X.t list ->       (* input 2 to merge *)
    'a M.t            (* result *)
end
