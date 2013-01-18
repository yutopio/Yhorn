open Types

type template = int list

val size_of_nf: pexpr nf -> int
val template_of_nf: 'a nf -> template
val size_of_tmpl: template -> int

val apply_template: template -> pexpr nf -> (pexpr * int * int) list list
val simplify: constr -> ?tmpl:template -> ?maxSize:int ->
  pexpr nf -> constr option
val unify: constr -> ?tmpl:template -> ?maxSize:int ->
  pexpr nf list -> constr option
