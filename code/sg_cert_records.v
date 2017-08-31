Require Import CAS.code.basic_types. 
Require Import CAS.code.eqv_certificates.
Require Import CAS.code.sg_certificates.
Require Import CAS.code.bs_certificates.

Set Implicit Arguments.
Unset Strict Implicit.

(* eqv *) 

Record eqv_certificates {S : Type} := {
  eqv_nontrivial    : assert_nontrivial (S := S)          
; eqv_congruence    : assert_brel_congruence (S := S) 
; eqv_reflexive     : assert_reflexive (S := S) 
; eqv_symmetric     : assert_symmetric (S := S) 
; eqv_transitive    : assert_transitive (S := S)
}.


(* orders *) 

(* quasi-order *) 
Record qo_certificates {S : Type}  := {
  qo_congruence      : assert_brel_congruence (S := S) 
; qo_reflexive       : assert_reflexive (S := S) 
; qo_transitive      : assert_transitive (S := S)
; qo_antisymmetric_d : check_antisymmetric (S := S) 
; qo_total_d         : check_total (S := S) 
}.

(* partial-order *) 
Record po_certificates {S : Type} := {
  po_congruence    : assert_brel_congruence (S := S) 
; po_reflexive     : assert_reflexive (S := S) 
; po_transitive    : assert_transitive (S := S)
; po_antisymmetric : assert_antisymmetric (S := S) 
; po_total_d       : check_total (S := S) 
}.

(* total-order *) 
Record to_certificates {S : Type} := {
  to_congruence    : assert_brel_congruence (S := S) 
; to_reflexive     : assert_reflexive (S := S) 
; to_transitive    : assert_transitive (S := S)
; to_antisymmetric : assert_antisymmetric (S := S) 
; to_total         : assert_total (S := S) 
}.


(* semigroups *) 

Record sg_certificates {S: Type}  := 
{
  sg_associative      : assert_associative (S := S) 
; sg_congruence       : assert_bop_congruence (S := S) 

; sg_commutative_d    : check_commutative (S := S) 
; sg_selective_d      : check_selective (S := S) 
; sg_idempotent_d     : check_idempotent (S := S) 
; sg_exists_id_d      : check_exists_id (S := S) 
; sg_exists_ann_d     : check_exists_ann (S := S) 

; sg_is_left_d        : check_is_left (S := S) 
; sg_is_right_d       : check_is_right (S := S) 

; sg_left_cancel_d    : check_left_cancellative (S := S) 
; sg_right_cancel_d   : check_right_cancellative (S := S) 
; sg_left_constant_d  : check_left_constant (S := S) 
; sg_right_constant_d : check_right_constant (S := S) 
; sg_anti_left_d      : check_anti_left (S := S) 
; sg_anti_right_d     : check_anti_right (S := S) 
}. 


Record sg_C_certificates {S: Type}  := 
{
  sg_C_associative      : assert_associative (S := S) 
; sg_C_congruence       : assert_bop_congruence (S := S) 
; sg_C_commutative      : assert_commutative (S := S) 
; sg_C_selective_d      : check_selective (S := S) 
; sg_C_idempotent_d     : check_idempotent (S := S)
; sg_C_exists_id_d      : check_exists_id (S := S) 
; sg_C_exists_ann_d     : check_exists_ann (S := S) 
; sg_C_left_cancel_d    : check_left_cancellative (S := S) 
; sg_C_right_cancel_d   : check_right_cancellative (S := S) 
; sg_C_left_constant_d  : check_left_constant (S := S) 
; sg_C_right_constant_d : check_right_constant (S := S) 
; sg_C_anti_left_d      : check_anti_left (S := S) 
; sg_C_anti_right_d     : check_anti_right (S := S) 
}. 

Record sg_CS_certificates {S: Type}  := 
{
  sg_CS_associative        : assert_associative (S := S) 
; sg_CS_congruence         : assert_bop_congruence (S := S) 
; sg_CS_commutative        : assert_commutative (S := S) 
; sg_CS_selective          : assert_selective (S := S) 
; sg_CS_exists_id_d        : check_exists_id (S := S) 
; sg_CS_exists_ann_d       : check_exists_ann (S := S) 
}. 

Record sg_CI_certificates {S: Type}  := 
{
  sg_CI_associative        : assert_associative (S := S) 
; sg_CI_congruence         : assert_bop_congruence (S := S) 
; sg_CI_commutative        : assert_commutative (S := S) 
; sg_CI_idempotent         : assert_idempotent (S := S) 
; sg_CI_selective_d        : check_selective (S := S) 
; sg_CI_exists_id_d        : check_exists_id (S := S) 
; sg_CI_exists_ann_d       : check_exists_ann (S := S) 
}. 

Record sg_CK_certificates {S: Type}  := 
{
  sg_CK_associative      : assert_associative (S := S) 
; sg_CK_congruence       : assert_bop_congruence (S := S) 
; sg_CK_commutative      : assert_commutative (S := S) 
; sg_CK_left_cancel      : assert_left_cancellative (S := S) 
; sg_CK_exists_id_d      : check_exists_id (S := S) 
; sg_CK_anti_left_d      : check_anti_left (S := S) 
; sg_CK_anti_right_d     : check_anti_right (S := S) 
}. 


(* ******************************************************************* *) 


Record bs_certificates {S: Type} := 
{
  bs_left_distributive_d      : check_left_distributive (S := S) 
; bs_right_distributive_d     : check_right_distributive (S := S) 
; bs_plus_id_is_times_ann_d   : check_plus_id_equals_times_ann (S := S) 
; bs_times_id_is_plus_ann_d   : check_times_id_equals_plus_ann (S := S) 
; bs_left_left_absorptive_d   : check_left_left_absorptive (S := S) 
; bs_left_right_absorptive_d  : check_left_right_absorptive (S := S) 
; bs_right_left_absorptive_d  : check_right_left_absorptive (S := S) 
; bs_right_right_absorptive_d : check_right_right_absorptive (S := S) 
}. 


