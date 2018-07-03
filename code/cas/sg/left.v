Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.

Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.ast.
Require Import CAS.code.eqv_records.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.sg_records.


Definition sg_certs_left : ∀ {S : Type},  S -> (S -> S) -> @sg_certificates S 
:= λ {S} s f,  
{|
  sg_associative      := Assert_Associative 
; sg_congruence       := Assert_Bop_Congruence 
; sg_commutative_d    := Certify_Not_Commutative (s, f s)
; sg_selective_d      := Certify_Selective 
; sg_is_left_d        := Certify_Is_Left 
; sg_is_right_d       := Certify_Not_Is_Right (s, f s)
; sg_idempotent_d     := Certify_Idempotent 
; sg_exists_id_d      := Certify_Not_Exists_Id 
; sg_exists_ann_d     := Certify_Not_Exists_Ann 
; sg_left_cancel_d    := Certify_Not_Left_Cancellative  (s, (s, f s)) 
; sg_right_cancel_d   := Certify_Right_Cancellative 
; sg_left_constant_d  := Certify_Left_Constant 
; sg_right_constant_d := Certify_Not_Right_Constant  (s, (s, f s)) 
; sg_anti_left_d      := Certify_Not_Anti_Left  (s, s) 
; sg_anti_right_d     := Certify_Not_Anti_Right  (s, s) 
|}. 



Definition sg_left: ∀ {S : Type},  @eqv S -> @sg S
:= λ {S} eqvS, 
   {| 
     sg_eq      := eqvS
   ; sg_bop     := bop_left 
   ; sg_certs   := sg_certs_left (eqv_witness eqvS) (eqv_new eqvS) 
   ; sg_ast     := Ast_sg_left (eqv_ast eqvS)
   |}. 
