open Types

type template = int list

val size_of_nf: 'a nf -> int
val template_of_nf: 'a nf -> template
val size_of_tmpl: template -> int

val enumerate_application: ((int * 'a list) list -> unit) ->
  template -> 'a nf -> unit
val unify: ('a list -> 'b -> 'b) -> 'b -> ?tmpl:template -> ?maxSize:int ->
  'a nf list -> 'b option
