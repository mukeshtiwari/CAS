open Datatypes
open Basic_types
open Brel
open Cef
open Cert_records
open Certificates
open Check

val eqv_certs_eq_bool : bool eqv_certificates

val eqv_certs_eq_nat : int eqv_certificates

val eqv_certs_add_constant :
  cas_constant -> 'a1 eqv_certificates -> 'a1 with_constant eqv_certificates

val eqv_certs_brel_list : 'a1 eqv_certificates -> 'a1 list eqv_certificates

val eqv_certs_brel_set :
  'a1 brel -> 'a1 eqv_certificates -> 'a1 finite_set eqv_certificates

val assert_product_nontrivial :
  'a1 assert_nontrivial -> 'a2 assert_nontrivial -> ('a1*'a2)
  assert_nontrivial

val eqv_certs_product :
  'a1 eqv_certificates -> 'a2 eqv_certificates -> ('a1*'a2) eqv_certificates

val eqv_certs_sum :
  'a1 eqv_certificates -> 'a2 eqv_certificates -> ('a1, 'a2) sum
  eqv_certificates

val sg_CS_certs_and : bool sg_CS_certificates

val sg_CS_certs_or : bool sg_CS_certificates

val sg_CS_certs_min : int sg_CS_certificates

val sg_CS_certs_max : int sg_CS_certificates

val sg_CK_certs_plus : int sg_CK_certificates

val sg_C_certs_times : int sg_C_certificates

val sg_certs_concat : 'a1 eqv_certificates -> 'a1 list sg_certificates

val sg_certs_left : 'a1 eqv_certificates -> 'a1 sg_certificates

val sg_certs_right : 'a1 eqv_certificates -> 'a1 sg_certificates

val sg_certs_add_id :
  cas_constant -> 'a1 eqv_certificates -> 'a1 sg_certificates -> 'a1
  with_constant sg_certificates

val sg_C_certs_add_id :
  cas_constant -> 'a1 eqv_certificates -> 'a1 sg_C_certificates -> 'a1
  with_constant sg_C_certificates

val sg_CI_certs_add_id :
  cas_constant -> 'a1 eqv_certificates -> 'a1 sg_CI_certificates -> 'a1
  with_constant sg_CI_certificates

val sg_CS_certs_add_id :
  cas_constant -> 'a1 eqv_certificates -> 'a1 sg_CS_certificates -> 'a1
  with_constant sg_CS_certificates

val sg_certs_add_ann :
  cas_constant -> 'a1 eqv_certificates -> 'a1 sg_certificates -> 'a1
  with_constant sg_certificates

val sg_C_certs_add_ann :
  cas_constant -> 'a1 eqv_certificates -> 'a1 sg_C_certificates -> 'a1
  with_constant sg_C_certificates

val sg_CI_certs_add_ann :
  cas_constant -> 'a1 eqv_certificates -> 'a1 sg_CI_certificates -> 'a1
  with_constant sg_CI_certificates

val sg_CS_certs_add_ann :
  cas_constant -> 'a1 eqv_certificates -> 'a1 sg_CS_certificates -> 'a1
  with_constant sg_CS_certificates

val sg_certs_left_sum :
  'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_certificates -> 'a2
  sg_certificates -> ('a1, 'a2) sum sg_certificates

val sg_certs_right_sum :
  'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_certificates -> 'a2
  sg_certificates -> ('a1, 'a2) sum sg_certificates

val sg_C_certs_left_sum :
  'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_C_certificates ->
  'a2 sg_C_certificates -> ('a1, 'a2) sum sg_C_certificates

val sg_C_certs_right_sum :
  'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_C_certificates ->
  'a2 sg_C_certificates -> ('a1, 'a2) sum sg_C_certificates

val sg_CI_certs_left_sum :
  'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_CI_certificates ->
  'a2 sg_CI_certificates -> ('a1, 'a2) sum sg_CI_certificates

val sg_CI_certs_right_sum :
  'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_CI_certificates ->
  'a2 sg_CI_certificates -> ('a1, 'a2) sum sg_CI_certificates

val sg_CS_certs_left_sum :
  'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_CS_certificates ->
  'a2 sg_CS_certificates -> ('a1, 'a2) sum sg_CS_certificates

val sg_CS_certs_right_sum :
  'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_CS_certificates ->
  'a2 sg_CS_certificates -> ('a1, 'a2) sum sg_CS_certificates

val sg_certs_product :
  'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_certificates -> 'a2
  sg_certificates -> ('a1*'a2) sg_certificates

val sg_certs_product_new :
  'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_certificates_new ->
  'a2 sg_certificates_new -> ('a1*'a2) sg_certificates_new

val sg_C_certs_product :
  'a1 brel -> 'a2 brel -> 'a1 binary_op -> 'a2 binary_op -> 'a1
  eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_C_certificates -> 'a2
  sg_C_certificates -> ('a1*'a2) sg_C_certificates

val sg_CI_certs_product :
  'a1 brel -> 'a2 brel -> 'a1 binary_op -> 'a2 binary_op -> 'a1
  eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_CI_certificates -> 'a2
  sg_CI_certificates -> ('a1*'a2) sg_CI_certificates

val sg_certs_llex :
  'a1 brel -> 'a1 binary_op -> 'a1 eqv_certificates -> 'a2 eqv_certificates
  -> 'a1 sg_CS_certificates -> 'a2 sg_certificates -> ('a1*'a2)
  sg_certificates

val sg_C_certs_llex :
  'a1 brel -> 'a1 binary_op -> 'a1 eqv_certificates -> 'a2 eqv_certificates
  -> 'a1 sg_CS_certificates -> 'a2 sg_C_certificates -> ('a1*'a2)
  sg_C_certificates

val sg_CI_certs_llex :
  'a1 brel -> 'a1 binary_op -> 'a1 eqv_certificates -> 'a2 eqv_certificates
  -> 'a1 sg_CS_certificates -> 'a2 sg_CI_certificates -> ('a1*'a2)
  sg_CI_certificates

val sg_CS_certs_llex :
  'a1 brel -> 'a1 binary_op -> 'a1 eqv_certificates -> 'a2 eqv_certificates
  -> 'a1 sg_CS_certificates -> 'a2 sg_CS_certificates -> ('a1*'a2)
  sg_CS_certificates

val sg_CI_certs_union_with_ann :
  cas_constant -> 'a1 eqv_certificates -> 'a1 finite_set with_constant
  sg_CI_certificates

val sg_CI_certs_intersect_with_id :
  cas_constant -> 'a1 eqv_certificates -> 'a1 finite_set with_constant
  sg_CI_certificates

val sg_sg_certs_add_zero :
  'a1 eqv_certificates -> 'a1 sg_sg_certificates -> 'a1 with_constant
  sg_sg_certificates

val bops_add_one_left_distributive_check :
  cas_constant -> 'a1 check_idempotent -> 'a1 check_left_absorptive -> 'a1
  check_left_distributive -> 'a1 with_constant check_left_distributive

val bops_add_one_right_distributive_check :
  cas_constant -> 'a1 check_idempotent -> 'a1 check_right_absorptive -> 'a1
  check_right_distributive -> 'a1 with_constant check_right_distributive

val bops_add_one_left_absorptive_check :
  cas_constant -> 'a1 check_idempotent -> 'a1 check_left_absorptive -> 'a1
  with_constant check_left_absorptive

val bops_add_one_right_absorptive_check :
  cas_constant -> 'a1 check_idempotent -> 'a1 check_right_absorptive -> 'a1
  with_constant check_right_absorptive

val sg_sg_certs_add_one :
  cas_constant -> 'a1 eqv_certificates -> 'a1 sg_C_certificates -> 'a1
  sg_sg_certificates -> 'a1 with_constant sg_sg_certificates

val sg_sg_certs_product :
  'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_sg_certificates ->
  'a2 sg_sg_certificates -> ('a1*'a2) sg_sg_certificates

val sg_sg_certs_llex_product :
  'a1 brel -> 'a2 brel -> 'a1 binary_op -> 'a2 binary_op -> 'a2 binary_op ->
  'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_certificates -> 'a2
  sg_certificates -> 'a1 sg_sg_certificates -> 'a2 sg_sg_certificates ->
  ('a1*'a2) sg_sg_certificates

