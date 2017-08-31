Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.

Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.ast.
Require Import CAS.code.eqv_records.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.sg_records.

Require Import CAS.code.cas.eqv.list.

Definition sg_certs_concat : ∀ {S : Type},  eqv_certificates (S := S) -> sg_certificates (S := (list S))
:= λ {S} eqvS,  
let (s, t) := nontrivial_pair (eqv_nontrivial eqvS) in 
{|
  sg_associative      := Assert_Associative 
; sg_congruence       := Assert_Bop_Congruence 
; sg_commutative_d    := Certify_Not_Commutative  (s :: nil, t :: nil)
; sg_selective_d      := Certify_Not_Selective (s :: nil, t :: nil)
; sg_is_left_d        := Certify_Not_Is_Left (nil, s :: nil)
; sg_is_right_d       := Certify_Not_Is_Right  (s :: nil, nil)
; sg_idempotent_d     := Certify_Not_Idempotent  (s :: nil)
; sg_exists_id_d      := Certify_Exists_Id  nil 
; sg_exists_ann_d     := Certify_Not_Exists_Ann  
; sg_left_cancel_d    := Certify_Left_Cancellative  
; sg_right_cancel_d   := Certify_Right_Cancellative  
; sg_left_constant_d  := Certify_Not_Left_Constant   (nil, (nil, s :: nil))
; sg_right_constant_d := Certify_Not_Right_Constant  (nil, (nil, s :: nil))
; sg_anti_left_d      := Certify_Not_Anti_Left  (s :: nil, nil) 
; sg_anti_right_d     := Certify_Not_Anti_Right  (s :: nil, nil)
|}. 

Definition sg_concat: ∀ {S : Type},  eqv (S := S) -> sg (S := (list S)) 
:= λ {S} eqvS, 
   {| 
     sg_eq     := eqv_list eqvS 
   ; sg_bop    := bop_concat 
   ; sg_certs  := sg_certs_concat (eqv_certs eqvS) 
   ; sg_ast    := Ast_sg_concat (eqv_ast eqvS)
   |}. 

