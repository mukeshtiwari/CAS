open Datatypes
open Peano
open Basic_types
open Brel
open Uop

val bop_and : bool binary_op

val bop_or : bool binary_op

val bop_plus : int binary_op

val bop_times : int binary_op

val bop_min : int binary_op

val bop_max : int binary_op

val bop_left : 'a1 binary_op

val bop_right : 'a1 binary_op

val bop_concat : 'a1 list binary_op

val bop_then_unary : 'a1 unary_op -> 'a1 binary_op -> 'a1 binary_op

val bop_product : 'a1 binary_op -> 'a2 binary_op -> ('a1*'a2) binary_op

val bop_left_sum : 'a1 binary_op -> 'a2 binary_op -> ('a1, 'a2) sum binary_op

val bop_right_sum :
  'a1 binary_op -> 'a2 binary_op -> ('a1, 'a2) sum binary_op

val bop_add_id :
  'a1 binary_op -> cas_constant -> (cas_constant, 'a1) sum binary_op

val bop_add_ann :
  'a1 binary_op -> cas_constant -> (cas_constant, 'a1) sum binary_op

val bop_llex :
  'a1 brel -> 'a1 binary_op -> 'a2 binary_op -> ('a1*'a2) binary_op

val bop_union : 'a1 brel -> 'a1 finite_set binary_op

val bop_intersect : 'a1 brel -> 'a1 finite_set binary_op

