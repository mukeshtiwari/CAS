open Datatypes
open Basic_types
open Cef
open Certificates

val bop_add_ann_commutative_check :
  'a1 check_commutative -> 'a1 with_constant check_commutative

val bop_add_ann_selective_check :
  'a1 check_selective -> 'a1 with_constant check_selective

val bop_add_ann_idempotent_check :
  'a1 check_idempotent -> 'a1 with_constant check_idempotent

val bop_add_ann_exists_id_check :
  'a1 check_exists_id -> 'a1 with_constant check_exists_id

val bop_add_ann_not_is_left_check :
  cas_constant -> 'a1 certify_witness -> 'a1 with_constant check_is_left

val bop_add_ann_not_is_right_check :
  cas_constant -> 'a1 certify_witness -> 'a1 with_constant check_is_right

val bop_add_id_commutative_check :
  'a1 check_commutative -> 'a1 with_constant check_commutative

val bop_add_id_selective_check :
  'a1 check_selective -> 'a1 with_constant check_selective

val bop_add_id_idempotent_check :
  'a1 check_idempotent -> 'a1 with_constant check_idempotent

val bop_add_id_exists_ann_check :
  'a1 check_exists_ann -> 'a1 with_constant check_exists_ann

val bop_add_id_not_is_left_check :
  cas_constant -> 'a1 certify_witness -> 'a1 with_constant check_is_left

val bop_add_id_not_is_right_check :
  cas_constant -> 'a1 certify_witness -> 'a1 with_constant check_is_right

val bop_add_id_left_cancellative_check :
  cas_constant -> 'a1 check_anti_left -> 'a1 check_left_cancellative -> 'a1
  with_constant check_left_cancellative

val bop_add_id_right_cancellative_check :
  cas_constant -> 'a1 check_anti_right -> 'a1 check_right_cancellative -> 'a1
  with_constant check_right_cancellative

val check_commutative_product :
  'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1 check_commutative ->
  'a2 check_commutative -> ('a1*'a2) check_commutative

val check_commutative_product_new :
  'a1 -> 'a2 -> (unit, 'a1*'a1) sum -> (unit, 'a2*'a2) sum -> (unit,
  ('a1*'a2)*('a1*'a2)) sum

val check_left_cancellative_product :
  'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1
  check_left_cancellative -> 'a2 check_left_cancellative -> ('a1*'a2)
  check_left_cancellative

val check_left_cancellative_product_new :
  'a1 -> 'a2 -> (unit, 'a1*('a1*'a1)) sum -> (unit, 'a2*('a2*'a2)) sum ->
  (unit, ('a1*'a2)*(('a1*'a2)*('a1*'a2))) sum

val check_right_cancellative_product :
  'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1
  check_right_cancellative -> 'a2 check_right_cancellative -> ('a1*'a2)
  check_right_cancellative

val check_right_cancellative_product_new :
  'a1 -> 'a2 -> (unit, 'a1*('a1*'a1)) sum -> (unit, 'a2*('a2*'a2)) sum ->
  (unit, ('a1*'a2)*(('a1*'a2)*('a1*'a2))) sum

val check_left_constant_product :
  'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1 check_left_constant
  -> 'a2 check_left_constant -> ('a1*'a2) check_left_constant

val check_left_constant_product_new :
  'a1 -> 'a2 -> (unit, 'a1*('a1*'a1)) sum -> (unit, 'a2*('a2*'a2)) sum ->
  (unit, ('a1*'a2)*(('a1*'a2)*('a1*'a2))) sum

val check_right_constant_product :
  'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1 check_right_constant
  -> 'a2 check_right_constant -> ('a1*'a2) check_right_constant

val check_right_constant_product_new :
  'a1 -> 'a2 -> (unit, 'a1*('a1*'a1)) sum -> (unit, 'a2*('a2*'a2)) sum ->
  (unit, ('a1*'a2)*(('a1*'a2)*('a1*'a2))) sum

val check_anti_left_product :
  'a1 check_anti_left -> 'a2 check_anti_left -> ('a1*'a2) check_anti_left

val check_anti_left_product_new :
  (unit, 'a1*'a1) sum -> (unit, 'a2*'a2) sum -> (unit, ('a1*'a2)*('a1*'a2))
  sum

val check_anti_right_product :
  'a1 check_anti_right -> 'a2 check_anti_right -> ('a1*'a2) check_anti_right

val check_anti_right_product_new :
  (unit, 'a1*'a1) sum -> (unit, 'a2*'a2) sum -> (unit, ('a1*'a2)*('a1*'a2))
  sum

val check_idempotent_product :
  'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1 check_idempotent ->
  'a2 check_idempotent -> ('a1*'a2) check_idempotent

val check_idempotent_product_new :
  'a1 -> 'a2 -> (unit, 'a1) sum -> (unit, 'a2) sum -> (unit, 'a1*'a2) sum

val check_is_left_product :
  'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1 check_is_left -> 'a2
  check_is_left -> ('a1*'a2) check_is_left

val check_is_left_product_new :
  'a1 -> 'a2 -> (unit, 'a1*'a1) sum -> (unit, 'a2*'a2) sum -> (unit,
  ('a1*'a2)*('a1*'a2)) sum

val check_is_right_product :
  'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1 check_is_right -> 'a2
  check_is_right -> ('a1*'a2) check_is_right

val check_is_right_product_new :
  'a1 -> 'a2 -> (unit, 'a1*'a1) sum -> (unit, 'a2*'a2) sum -> (unit,
  ('a1*'a2)*('a1*'a2)) sum

val check_selective_product :
  'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1 check_is_left -> 'a2
  check_is_left -> 'a1 check_is_right -> 'a2 check_is_right -> ('a1*'a2)
  check_selective

val check_selective_product_new :
  'a1 -> 'a2 -> (unit, 'a1*'a1) sum -> (unit, 'a2*'a2) sum -> (unit, 'a1*'a1)
  sum -> (unit, 'a2*'a2) sum -> (unit, ('a1*'a2)*('a1*'a2)) sum

val check_exists_id_product :
  'a1 check_exists_id -> 'a2 check_exists_id -> ('a1*'a2) check_exists_id

val check_exists_id_product_new :
  ('a1, unit) sum -> ('a2, unit) sum -> ('a1*'a2, unit) sum

val check_exists_ann_product :
  'a1 check_exists_ann -> 'a2 check_exists_ann -> ('a1*'a2) check_exists_ann

val check_exists_ann_product_new :
  ('a1, unit) sum -> ('a2, unit) sum -> ('a1*'a2, unit) sum

val bop_product_left_distributive_check :
  'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1
  check_left_distributive -> 'a2 check_left_distributive -> ('a1*'a2)
  check_left_distributive

val bop_product_right_distributive_check :
  'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1
  check_right_distributive -> 'a2 check_right_distributive -> ('a1*'a2)
  check_right_distributive

val bop_product_plus_id_is_times_ann_check :
  'a1 check_plus_id_equals_times_ann -> 'a2 check_plus_id_equals_times_ann ->
  ('a1*'a2) check_plus_id_equals_times_ann

val bop_product_times_id_equals_plus_ann_check :
  'a1 check_times_id_equals_plus_ann -> 'a2 check_times_id_equals_plus_ann ->
  ('a1*'a2) check_times_id_equals_plus_ann

val bop_product_left_absorptive_check :
  'a1 -> 'a2 -> 'a1 check_left_absorptive -> 'a2 check_left_absorptive ->
  ('a1*'a2) check_left_absorptive

val bop_product_right_absorptive_check :
  'a1 -> 'a2 -> 'a1 check_right_absorptive -> 'a2 check_right_absorptive ->
  ('a1*'a2) check_right_absorptive

val check_commutative_llex :
  'a1 assert_nontrivial -> 'a2 check_commutative -> ('a1*'a2)
  check_commutative

val check_idempotent_llex :
  'a1 assert_nontrivial -> 'a2 check_idempotent -> ('a1*'a2) check_idempotent

val check_selective_llex :
  'a1 assert_nontrivial -> 'a2 check_selective -> ('a1*'a2) check_selective

val check_exists_id_llex :
  'a1 check_exists_id -> 'a2 check_exists_id -> ('a1*'a2) check_exists_id

val check_exists_ann_llex :
  'a1 check_exists_ann -> 'a2 check_exists_ann -> ('a1*'a2) check_exists_ann

val bops_llex_product_left_distributive_check :
  'a1 brel -> 'a2 brel -> 'a1 binary_op -> 'a2 binary_op -> 'a2 binary_op ->
  'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1
  check_left_cancellative -> 'a2 check_left_constant -> 'a1
  check_left_distributive -> 'a2 check_left_distributive -> ('a1*'a2)
  check_left_distributive

val bops_llex_product_right_distributive_check :
  'a1 brel -> 'a2 brel -> 'a1 binary_op -> 'a2 binary_op -> 'a2 binary_op ->
  'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1
  check_right_cancellative -> 'a2 check_right_constant -> 'a1
  check_right_distributive -> 'a2 check_right_distributive -> ('a1*'a2)
  check_right_distributive

val bops_llex_product_plus_id_is_times_ann_check :
  'a1 check_plus_id_equals_times_ann -> 'a2 check_plus_id_equals_times_ann ->
  ('a1*'a2) check_plus_id_equals_times_ann

val bops_llex_product_times_id_equals_plus_ann_check :
  'a1 check_times_id_equals_plus_ann -> 'a2 check_times_id_equals_plus_ann ->
  ('a1*'a2) check_times_id_equals_plus_ann

val bops_llex_product_left_absorptive_check :
  'a2 -> 'a1 check_left_absorptive -> 'a2 check_left_absorptive -> 'a1
  check_anti_left -> ('a1*'a2) check_left_absorptive

val bops_llex_product_right_absorptive_check :
  'a2 -> 'a1 check_right_absorptive -> 'a2 check_right_absorptive -> 'a1
  check_anti_right -> ('a1*'a2) check_right_absorptive

val bops_add_zero_left_distributive_check :
  'a1 check_left_distributive -> 'a1 with_constant check_left_distributive

val bops_add_zero_right_distributive_check :
  'a1 check_right_distributive -> 'a1 with_constant check_right_distributive

val bops_add_zero_left_absorptive_check :
  'a1 -> 'a1 check_left_absorptive -> 'a1 with_constant check_left_absorptive

val bops_add_zero_right_absorptive_check :
  'a1 -> 'a1 check_right_absorptive -> 'a1 with_constant
  check_right_absorptive

val check_commutative_sum :
  'a1 check_commutative -> 'a2 check_commutative -> ('a1, 'a2) sum
  check_commutative

val check_idempotent_sum :
  'a1 check_idempotent -> 'a2 check_idempotent -> ('a1, 'a2) sum
  check_idempotent

val check_selective_sum :
  'a1 check_selective -> 'a2 check_selective -> ('a1, 'a2) sum
  check_selective

val check_exists_id_left_sum :
  'a2 check_exists_id -> ('a1, 'a2) sum check_exists_id

val check_exists_id_right_sum :
  'a1 check_exists_id -> ('a1, 'a2) sum check_exists_id

val check_exists_ann_left_sum :
  'a1 check_exists_ann -> ('a1, 'a2) sum check_exists_ann

val check_exists_ann_right_sum :
  'a2 check_exists_ann -> ('a1, 'a2) sum check_exists_ann

