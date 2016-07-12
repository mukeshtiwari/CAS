open Basic_types
open Brel

val uop_duplicate_elim : 'a1 brel -> 'a1 finite_set unary_op

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val uop_filter : 'a1 bProp -> 'a1 finite_set unary_op

