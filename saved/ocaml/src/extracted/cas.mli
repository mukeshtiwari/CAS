open Datatypes
open Ast
open Basic_types
open Bop
open Brel
open Cas_records
open Construct_certs

val eqv_eq_bool : bool eqv

val eqv_eq_nat : int eqv

val eqv_add_constant : 'a1 eqv -> cas_constant -> 'a1 with_constant eqv

val eqv_list : 'a1 eqv -> 'a1 list eqv

val eqv_set : 'a1 eqv -> 'a1 finite_set eqv

val eqv_product : 'a1 eqv -> 'a2 eqv -> ('a1*'a2) eqv

val eqv_sum : 'a1 eqv -> 'a2 eqv -> ('a1, 'a2) sum eqv

val sg_C_times : int sg_C

val sg_CK_plus : int sg_CK

val sg_CS_and : bool sg_CS

val sg_CS_or : bool sg_CS

val sg_CS_min : int sg_CS

val sg_CS_max : int sg_CS

val sg_concat : 'a1 eqv -> 'a1 list sg

val sg_left : 'a1 eqv -> 'a1 sg

val sg_right : 'a1 eqv -> 'a1 sg

val sg_add_id : cas_constant -> 'a1 sg -> 'a1 with_constant sg

val sg_C_add_id : cas_constant -> 'a1 sg_C -> 'a1 with_constant sg_C

val sg_CI_add_id : cas_constant -> 'a1 sg_CI -> 'a1 with_constant sg_CI

val sg_CS_add_id : cas_constant -> 'a1 sg_CS -> 'a1 with_constant sg_CS

val sg_add_ann : cas_constant -> 'a1 sg -> 'a1 with_constant sg

val sg_C_add_ann : cas_constant -> 'a1 sg_C -> 'a1 with_constant sg_C

val sg_CI_add_ann : cas_constant -> 'a1 sg_CI -> 'a1 with_constant sg_CI

val sg_CS_add_ann : cas_constant -> 'a1 sg_CS -> 'a1 with_constant sg_CS

val sg_product : 'a1 sg -> 'a2 sg -> ('a1*'a2) sg

val sg_product_new : 'a1 sg_new -> 'a2 sg_new -> ('a1*'a2) sg_new

val sg_C_product : 'a1 sg_C -> 'a2 sg_C -> ('a1*'a2) sg_C

val sg_CI_product : 'a1 sg_CI -> 'a2 sg_CI -> ('a1*'a2) sg_CI

val sg_left_sum : 'a1 sg -> 'a2 sg -> ('a1, 'a2) sum sg

val sg_right_sum : 'a1 sg -> 'a2 sg -> ('a1, 'a2) sum sg

val sg_C_left_sum : 'a1 sg_C -> 'a2 sg_C -> ('a1, 'a2) sum sg_C

val sg_C_right_sum : 'a1 sg_C -> 'a2 sg_C -> ('a1, 'a2) sum sg_C

val sg_CI_left_sum : 'a1 sg_CI -> 'a2 sg_CI -> ('a1, 'a2) sum sg_CI

val sg_CI_right_sum : 'a1 sg_CI -> 'a2 sg_CI -> ('a1, 'a2) sum sg_CI

val sg_CS_left_sum : 'a1 sg_CS -> 'a2 sg_CS -> ('a1, 'a2) sum sg_CS

val sg_CS_right_sum : 'a1 sg_CS -> 'a2 sg_CS -> ('a1, 'a2) sum sg_CS

val sg_llex : 'a1 sg_CS -> 'a2 sg -> ('a1*'a2) sg

val sg_C_llex : 'a1 sg_CS -> 'a2 sg_C -> ('a1*'a2) sg_C

val sg_CI_llex : 'a1 sg_CS -> 'a2 sg_CI -> ('a1*'a2) sg_CI

val sg_CS_llex : 'a1 sg_CS -> 'a2 sg_CS -> ('a1*'a2) sg_CS

val sg_CI_union_with_ann :
  cas_constant -> 'a1 eqv -> 'a1 finite_set with_constant sg_CI

val sg_CI_intersect_with_id :
  cas_constant -> 'a1 eqv -> 'a1 finite_set with_constant sg_CI

val sg_CS_min_with_infinity : int with_constant sg_CS

val sg_CS_max_with_infinity : int with_constant sg_CS

val sg_sg_add_zero : 'a1 sg_sg -> cas_constant -> 'a1 with_constant sg_sg

val sg_C_sg_add_one :
  'a1 sg_C_sg -> cas_constant -> 'a1 with_constant sg_C_sg

val sg_sg_product : 'a1 sg_sg -> 'a2 sg_sg -> ('a1*'a2) sg_sg

val sg_C_sg_llex : 'a1 sg_CS_sg -> 'a2 sg_C_sg -> ('a1*'a2) sg_C_sg

val sg_CS_sg_llex : 'a1 sg_CS_sg -> 'a2 sg_CS_sg -> ('a1*'a2) sg_CS_sg

val sg_CI_sg_llex : 'a1 sg_CS_sg -> 'a2 sg_CI_sg -> ('a1*'a2) sg_CI_sg

