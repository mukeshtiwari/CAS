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


Record sg_certificates_new (S: Type)  := 
{
  sgn_commutative_d    : unit + (S * S) 
; sgn_selective_d      : unit + (S * S) 
; sgn_idempotent_d     : unit + S 
; sgn_exists_id_d      : S + unit 
; sgn_exists_ann_d     : S + unit 
; sgn_is_left_d        : unit + (S * S) 
; sgn_is_right_d       : unit + (S * S) 
; sgn_left_cancel_d    : unit + (S * (S * S)) 
; sgn_right_cancel_d   : unit + (S * (S * S)) 
; sgn_left_constant_d  : unit + (S * (S * S)) 
; sgn_right_constant_d : unit + (S * (S * S)) 
; sgn_anti_left_d      : unit + (S * S) 
; sgn_anti_right_d     : unit + (S * S) 
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


Record sg_sg_certificates (S: Type) := 
{
  sg_sg_left_distributive_d    : check_left_distributive S 
; sg_sg_right_distributive_d   : check_right_distributive S 
; sg_sg_plus_id_is_times_ann_d : check_plus_id_equals_times_ann S 
; sg_sg_times_id_is_plus_ann_d : check_times_id_equals_plus_ann S 
; sg_sg_left_absorptive_d      : check_left_absorptive S 
; sg_sg_right_absorptive_d     : check_right_absorptive S 
}. 


(* 
Record sg_sg_LD_certificates (S: Type) :=
{
  sg_sg_LD_left_distributive      : assert_left_distributive S 
; sg_sg_LD_left_absorption_d      : check_left_absorptive S 
; sg_sg_LD_right_absorption_d     : check_right_absorptive S 
; sg_sg_LD_plus_id_is_times_ann_d : check_plus_id_equals_times_ann S 
; sg_sg_LD_times_id_is_plus_ann_d : check_times_id_equals_plus_ann S 
}. 

Record sg_sg_LA_certificates (S: Type) := 
{
  sg_sg_LA_left_distributive_d    : check_left_distributive S 
; sg_sg_LA_right_distributive_d   : check_right_distributive S 
; sg_sg_LA_left_absorption        : assert_left_absorptive S 
; sg_sg_LA_plus_id_is_times_ann_d : check_plus_id_equals_times_ann S 
; sg_sg_LA_times_id_is_plus_ann_d : check_times_id_equals_plus_ann S 
}. 

Record sg_sg_LALD_certificates (S: Type) := 
{
  sg_sg_LALD_left_distributive      : assert_left_distributive S 
; sg_sg_LALD_left_absorption        : assert_left_absoprtion S 
; sg_sg_LALD_plus_id_is_times_ann_d : check_plus_id_equals_times_ann S 
; sg_sg_LALD_times_id_is_plus_ann_d : check_times_id_equals_plus_ann S 
}. 

*) 
(* ******************************************************************* *) 

