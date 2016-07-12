open Basic_types
open Brel

val cef_commutative_implies_not_is_left :
  'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a1*'a1

val cef_commutative_implies_not_is_right :
  'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a1*'a1

val cef_selective_and_commutative_imply_not_left_cancellative :
  'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a1*('a1*'a1)

val cef_selective_and_commutative_imply_not_right_cancellative :
  'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a1*('a1*'a1)

val cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative :
  'a1 binary_op -> 'a1 -> 'a1 -> 'a1*('a1*'a1)

val cef_idempotent_and_commutative_and_not_selective_imply_not_right_cancellative :
  'a1 binary_op -> 'a1 -> 'a1 -> 'a1*('a1*'a1)

val cef_not_idempotent_implies_not_selective : 'a1 -> 'a1*'a1

val cef_left_cancellative_implies_not_left_constant :
  'a1 -> ('a1 -> 'a1) -> 'a1*('a1*'a1)

val cef_right_cancellative_implies_not_right_constant :
  'a1 -> ('a1 -> 'a1) -> 'a1*('a1*'a1)

val cef_cancellative_and_exists_id_imply_not_idempotent :
  'a1 brel -> 'a1 -> 'a1 -> ('a1 -> 'a1) -> 'a1

val cef_idempotent_and_commutative_imply_not_left_constant :
  'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a1*('a1*'a1)

val cef_idempotent_and_commutative_imply_not_right_constant :
  'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a1*('a1*'a1)

val cef_idempotent_implies_not_anti_left : 'a1 -> 'a1*'a1

val cef_idempotent_implies_not_anti_right : 'a1 -> 'a1*'a1

val cef_bop_llex_not_cancellative :
  'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a2 -> ('a2 -> 'a2) ->
  ('a1*'a2)*(('a1*'a2)*('a1*'a2))

val cef_bop_llex_not_anti_left :
  'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a2 ->
  ('a1*'a2)*('a1*'a2)

val cef_bop_llex_not_anti_right :
  'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a2 ->
  ('a1*'a2)*('a1*'a2)

val cef_bop_llex_not_constant :
  'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a2 -> ('a2 -> 'a2) ->
  ('a1*'a2)*(('a1*'a2)*('a1*'a2))

val cef_bop_llex_not_is_left :
  'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a2 ->
  ('a1*'a2)*('a1*'a2)

val cef_bop_llex_not_is_right :
  'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a2 ->
  ('a1*'a2)*('a1*'a2)

val cef_llex_product_not_left_distributive :
  'a1 brel -> 'a2 brel -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a1
  binary_op -> 'a2 binary_op -> 'a2 binary_op ->
  ('a1*'a2)*(('a1*'a2)*('a1*'a2))

val cef_llex_product_not_right_distributive :
  'a1 brel -> 'a2 brel -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a1
  binary_op -> 'a2 binary_op -> 'a2 binary_op ->
  ('a1*'a2)*(('a1*'a2)*('a1*'a2))

