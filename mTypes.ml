open MapEx

(*** Temporarily moved here. *)

module M = Map.Make(Id)
module S = Set.Make(Id)

module Integer = struct
  type t = int
  let compare = compare
  let hash x = x
  let equal = (=)
end

module MI = Map.Make(Integer)

module MyIntList = struct
  type t = int list
  let compare = compare
end

module MIL = Map.Make(MyIntList)
