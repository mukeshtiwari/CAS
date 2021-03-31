Require Import CAS.coq.common.compute. 
Require Import CAS.coq.common.sg_certificates.

Set Implicit Arguments.
Unset Strict Implicit.

Record sg_certificates {S: Type}  := 
{
  sg_associative      : assert_associative (S := S) 
; sg_congruence       : assert_bop_congruence (S := S) 

; sg_commutative_d    : check_commutative (S := S) 
; sg_selective_d      : check_selective (S := S) 
; sg_idempotent_d     : check_idempotent (S := S) 

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
; sg_C_cancel_d         : check_left_cancellative (S := S) 
; sg_C_constant_d       : check_left_constant (S := S) 
; sg_C_anti_left_d      : check_anti_left (S := S) 
; sg_C_anti_right_d     : check_anti_right (S := S)
}. 

Record sg_CS_certificates {S: Type}  := 
{
  sg_CS_associative        : assert_associative (S := S) 
; sg_CS_congruence         : assert_bop_congruence (S := S) 
; sg_CS_commutative        : assert_commutative (S := S) 
; sg_CS_selective          : assert_selective (S := S)
}. 

Record sg_CI_certificates {S: Type}  := 
{
  sg_CI_associative        : assert_associative (S := S) 
; sg_CI_congruence         : assert_bop_congruence (S := S) 
; sg_CI_commutative        : assert_commutative (S := S) 
; sg_CI_idempotent         : assert_idempotent (S := S) 
; sg_CI_selective_d        : check_selective (S := S)
}. 

Record sg_CK_certificates {S: Type}  := 
{
  sg_CK_associative      : assert_associative (S := S) 
; sg_CK_congruence       : assert_bop_congruence (S := S) 
; sg_CK_commutative      : assert_commutative (S := S) 
; sg_CK_left_cancel      : assert_left_cancellative (S := S) 
; sg_CK_anti_left_d      : check_anti_left (S := S) 
; sg_CK_anti_right_d     : check_anti_right (S := S)
}. 


Record asg_certificates {S: Type}  := 
{
  asg_associative      : assert_associative (S := S) 
; asg_congruence       : assert_bop_congruence (S := S) 
; asg_commutative      : assert_commutative (S := S) 
; asg_selective_d      : check_selective (S := S) 
; asg_idempotent_d     : check_idempotent (S := S)
}. 

Record msg_certificates {S: Type}  := 
{
  msg_associative      : assert_associative (S := S) 
; msg_congruence       : assert_bop_congruence (S := S) 

; msg_commutative_d    : check_commutative (S := S) 
; msg_is_left_d        : check_is_left (S := S) 
; msg_is_right_d       : check_is_right (S := S) 
; msg_left_cancel_d    : check_left_cancellative (S := S) 
; msg_right_cancel_d   : check_right_cancellative (S := S) 
; msg_left_constant_d  : check_left_constant (S := S) 
; msg_right_constant_d : check_right_constant (S := S) 
; msg_anti_left_d      : check_anti_left (S := S) 
; msg_anti_right_d     : check_anti_right (S := S)
}. 



