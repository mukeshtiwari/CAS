Require Import CAS.code.basic_types. 
Require Import CAS.code.certificates. 

(* eqv *) 

Record eqv_certificates (S : Type) := {
  eqv_nontrivial    : assert_nontrivial S          
; eqv_congruence    : assert_brel_congruence S 
; eqv_reflexive     : assert_reflexive S 
; eqv_symmetric     : assert_symmetric S 
; eqv_transitive    : assert_transitive S
}.


(* orders *) 

(* quasi-order *) 
Record qo_certificates (S : Type)  := {
  qo_congruence      : assert_brel_congruence S 
; qo_reflexive       : assert_reflexive S 
; qo_transitive      : assert_transitive S
; qo_antisymmetric_d : check_antisymmetric S 
; qo_total_d         : check_total S 
}.

(* partial-order *) 
Record po_certificates (S : Type) := {
  po_congruence    : assert_brel_congruence S 
; po_reflexive     : assert_reflexive S 
; po_transitive    : assert_transitive S
; po_antisymmetric : assert_antisymmetric S 
; po_total_d       : check_total S 
}.

(* total-order *) 
Record to_certificates (S : Type) := {
  to_congruence    : assert_brel_congruence S 
; to_reflexive     : assert_reflexive S 
; to_transitive    : assert_transitive S
; to_antisymmetric : assert_antisymmetric S 
; to_total         : assert_total S 
}.


(* semigroups *) 

Record sg_certificates (S: Type)  := 
{
  sg_associative      : assert_associative S 
; sg_congruence       : assert_bop_congruence S 

; sg_commutative_d    : check_commutative S 
; sg_selective_d      : check_selective S 
; sg_idempotent_d     : check_idempotent S 
; sg_exists_id_d      : check_exists_id S 
; sg_exists_ann_d     : check_exists_ann S 

; sg_is_left_d        : check_is_left S 
; sg_is_right_d       : check_is_right S 

; sg_left_cancel_d    : check_left_cancellative S 
; sg_right_cancel_d   : check_right_cancellative S 
; sg_left_constant_d  : check_left_constant S 
; sg_right_constant_d : check_right_constant S 
; sg_anti_left_d      : check_anti_left S 
; sg_anti_right_d     : check_anti_right S 
}. 


Record sg_C_certificates (S: Type)  := 
{
  sg_C_associative      : assert_associative S 
; sg_C_congruence       : assert_bop_congruence S 
; sg_C_commutative      : assert_commutative S 
; sg_C_selective_d      : check_selective S 
; sg_C_idempotent_d     : check_idempotent S
; sg_C_exists_id_d      : check_exists_id S 
; sg_C_exists_ann_d     : check_exists_ann S 
; sg_C_left_cancel_d    : check_left_cancellative S 
; sg_C_right_cancel_d   : check_right_cancellative S 
; sg_C_left_constant_d  : check_left_constant S 
; sg_C_right_constant_d : check_right_constant S 
; sg_C_anti_left_d      : check_anti_left S 
; sg_C_anti_right_d     : check_anti_right S 
}. 

Record sg_CS_certificates (S: Type)  := 
{
  sg_CS_associative        : assert_associative S 
; sg_CS_congruence         : assert_bop_congruence S 
; sg_CS_commutative        : assert_commutative S 
; sg_CS_selective          : assert_selective S 
; sg_CS_exists_id_d        : check_exists_id S 
; sg_CS_exists_ann_d       : check_exists_ann S 
}. 

Record sg_CI_certificates (S: Type)  := 
{
  sg_CI_associative        : assert_associative S 
; sg_CI_congruence         : assert_bop_congruence S 
; sg_CI_commutative        : assert_commutative S 
; sg_CI_idempotent         : assert_idempotent S 
; sg_CI_selective_d        : check_selective S 
; sg_CI_exists_id_d        : check_exists_id S 
; sg_CI_exists_ann_d       : check_exists_ann S 
}. 

Record sg_CK_certificates (S: Type)  := 
{
  sg_CK_associative      : assert_associative S 
; sg_CK_congruence       : assert_bop_congruence S 
; sg_CK_commutative      : assert_commutative S 
; sg_CK_left_cancel      : assert_left_cancellative S 
; sg_CK_exists_id_d      : check_exists_id S 
; sg_CK_anti_left_d      : check_anti_left S 
; sg_CK_anti_right_d     : check_anti_right S 
}. 


(* ******************************************************************* *) 


Record bs_certificates (S: Type) := 
{
  bs_left_distributive_d      : check_left_distributive S 
; bs_right_distributive_d     : check_right_distributive S 
; bs_plus_id_is_times_ann_d   : check_plus_id_equals_times_ann S 
; bs_times_id_is_plus_ann_d   : check_times_id_equals_plus_ann S 
; bs_left_left_absorptive_d   : check_left_left_absorptive S 
; bs_left_right_absorptive_d  : check_left_right_absorptive S 
; bs_right_left_absorptive_d  : check_right_left_absorptive S 
; bs_right_right_absorptive_d : check_right_right_absorptive S 
}. 


