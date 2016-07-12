(*
open Basic_types
open Brel
*) 

(** val uop_duplicate_elim : 'a1 brel -> 'a1 finite_set unary_op **)

let uop_duplicate_elim r =
  let rec f = function
  | [] -> []
  | a::y -> if in_set r y a then f y else a::(f y)
  in f

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x::l0 -> if f x then x::(filter f l0) else filter f l0

(** val uop_filter : 'a1 bProp -> 'a1 finite_set unary_op **)

let uop_filter =
  filter

