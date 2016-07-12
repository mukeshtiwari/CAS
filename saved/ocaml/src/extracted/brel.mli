open Bool
open Datatypes
open EqNat
open Basic_types

val cas_infinity : cas_constant

val brel_eq_bool : bool brel

val brel_eq_nat : int brel

val brel_dual : 'a1 brel -> 'a1 brel

val brel_list : 'a1 brel -> 'a1 list brel

val brel_product : 'a1 brel -> 'a2 brel -> ('a1*'a2) brel

val brel_sum : 'a1 brel -> 'a2 brel -> ('a1, 'a2) sum brel

val brel_add_constant :
  'a1 brel -> cas_constant -> (cas_constant, 'a1) sum brel

val brel_conjunction : 'a1 brel -> 'a1 brel -> 'a1 brel

val brel_llte : 'a1 brel -> 'a1 binary_op -> 'a1 brel

val brel_llt : 'a1 brel -> 'a1 binary_op -> 'a1 brel

val brel_and_sym : 'a1 brel -> 'a1 brel

val in_set : 'a1 brel -> ('a1 finite_set, 'a1) brel2

val brel_subset : 'a1 brel -> 'a1 finite_set brel

val brel_set : 'a1 brel -> 'a1 finite_set brel

