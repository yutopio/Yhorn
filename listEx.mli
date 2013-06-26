
module List : sig

val length : 'a list -> int
val hd : 'a list -> 'a
val tl : 'a list -> 'a list
val nth : 'a list -> int -> 'a
val rev : 'a list -> 'a list
val append : 'a list -> 'a list -> 'a list
val rev_append : 'a list -> 'a list -> 'a list
val concat : 'a list list -> 'a list
val flatten : 'a list list -> 'a list
val iter : ('a -> unit) -> 'a list -> unit
val iteri : (int -> 'a -> unit) -> 'a list -> unit
val map : ('a -> 'b) -> 'a list -> 'b list
val mapi : (int -> 'a -> 'b) -> 'a list -> 'b list
val rev_map : ('a -> 'b) -> 'a list -> 'b list
val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
val fold_right : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
val iter2 : ('a -> 'b -> unit) -> 'a list -> 'b list -> unit
val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
val rev_map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
val fold_right2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
val for_all : ('a -> bool) -> 'a list -> bool
val exists : ('a -> bool) -> 'a list -> bool
val for_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
val exists2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
val mem : 'a -> 'a list -> bool
val memq : 'a -> 'a list -> bool
val find : ('a -> bool) -> 'a list -> 'a
val filter : ('a -> bool) -> 'a list -> 'a list
val find_all : ('a -> bool) -> 'a list -> 'a list
val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
val assoc : 'a -> ('a * 'b) list -> 'b
val assq : 'a -> ('a * 'b) list -> 'b
val mem_assoc : 'a -> ('a * 'b) list -> bool
val mem_assq : 'a -> ('a * 'b) list -> bool
val remove_assoc : 'a -> ('a * 'b) list -> ('a * 'b) list
val remove_assq : 'a -> ('a * 'b) list -> ('a * 'b) list
val split : ('a * 'b) list -> 'a list * 'b list
val combine : 'a list -> 'b list -> ('a * 'b) list
val sort : ('a -> 'a -> int) -> 'a list -> 'a list
val stable_sort : ('a -> 'a -> int) -> 'a list -> 'a list
val fast_sort : ('a -> 'a -> int) -> 'a list -> 'a list
val merge : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list

  val remove : 'a -> 'a list -> 'a list
  (** Removes the first occurrence of a specific element from the List. *)

  val remove_at : int -> 'a list -> 'a list
  (** Removes the element at the specified index of the List. *)

  val index_of : 'a -> 'a list -> int
  (** [index_of x l] returns the first index of an occurrence of element [x] in
      the list [l]. Raise [Not_found] if [x] does not exists in the list. *)

  val reduce : ('a -> 'a -> 'a) -> 'a list -> 'a
  (** [reduce f [ x1 ; x2 ; ...; xn] ] is [f ... (f (f x1 x2) x3) ... xn].
      Raise [Failure "reduce"] if the list is empty. *)

  val max : 'a list -> 'a
  (** Choose the maximum value among the list. Raise [Failure "max"] if the
      list is empty. *)

  val min : 'a list -> 'a
  (** Choose the minimum value among the list. Raise [Failure "min"] if the
      list is empty. *)

  val try_pick : ('a -> 'b option) -> 'a list -> 'b option
  (** Apply a function to each element in the list and pick the first result
      that is not None. *)

  val distinct : 'a list -> 'a list
  (** Returns distinct elements from a list. *)

  val sort_distinct : 'a list -> 'a list
  (** Sort the list and then returns distinct elements from it. *)

  val skip : int -> 'a list -> 'a list
  (** Bypasses a specified number of elements in the list and then returns the
      remaining elements. *)

  val take : int -> 'a list -> 'a list
  (** Returns a specified number of contiguous elements from the start of a
      list. *)

  val chop : int -> 'a list -> 'a list list
  (** Chop the list so that each sub-list is no longer than a specified
      number. *)

  val direct_product : 'a list list -> 'a list list
  (** Gets the all possible combinations of elements each of those are chosen
      from every list. For example, [direct_product [[A;B]; [C;D]]] returns
      [[A;C]; [A;D]; [B;C]; [B;D]]. *)

  val sorted_multimap :
    ('a -> 'a -> int) ->
    ('a -> (int * 'b) list -> 'c option) ->
    ('a * 'b) list list -> ('a * 'c) list
  (** Transform values of multiple association lists with the same key type,
      and returns a new association list. [sorted_multimap compare f lists]
      uses [comapre] for association key comparison and [f] transforms each
      value(s) appearing in given [lists]. Returning None for it will remove
      the association from the returning list. It requires that all association
      lists in [lists] must be sorted with key according to [compare]. *)
end
