Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.

Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.ast.
Require Import CAS.code.eqv_records.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.sg_records.


Definition sg_certs_right : ∀ {S : Type},  S -> (S -> S) -> sg_certificates (S := S) 
:= λ {S} s f,  
{|
  sg_associative   := Assert_Associative 
; sg_congruence    := Assert_Bop_Congruence 
; sg_commutative_d := Certify_Not_Commutative (f s, s)
; sg_selective_d   := Certify_Selective 
; sg_is_left_d     := Certify_Not_Is_Left (f s, s)
; sg_is_right_d    := Certify_Is_Right 
; sg_idempotent_d  := Certify_Idempotent 
; sg_exists_id_d   := Certify_Not_Exists_Id  
; sg_exists_ann_d  := Certify_Not_Exists_Ann 
; sg_left_cancel_d    := Certify_Left_Cancellative
; sg_right_cancel_d   := Certify_Not_Right_Cancellative (s, (s, f s))
; sg_left_constant_d  := Certify_Not_Left_Constant (s, (s, f s))
; sg_right_constant_d := Certify_Right_Constant
; sg_anti_left_d      := Certify_Not_Anti_Left (s, s) 
; sg_anti_right_d     := Certify_Not_Anti_Right (s, s) 
|}. 



Definition sg_right : ∀ {S : Type},  eqv (S := S) -> sg (S := S) 
:= λ {S} eqvS, 
   {| 
     sg_eq     := eqvS
   ; sg_bop    := bop_right 
   ; sg_certs  := sg_certs_right (eqv_witness eqvS) (eqv_new eqvS) 
   ; sg_ast    := Ast_sg_right (eqv_ast eqvS)
   |}. 
