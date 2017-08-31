Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.

Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.eqv_records.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.bs_certificates.
Require Import CAS.code.bs_cert_records.
Require Import CAS.code.bs_records.
Require Import CAS.code.ast.

Require Import CAS.code.cas.eqv.nat.
Require Import CAS.code.cas.sg.max.
Require Import CAS.code.cas.sg.plus.

Definition bs_certs_max_plus : bs_certificates (S := nat) := 
  {| 
     bs_left_distributive_d      := Certify_Left_Distributive 
   ; bs_right_distributive_d     := Certify_Right_Distributive 
   ; bs_plus_id_is_times_ann_d   := Certify_Not_Plus_Id_Equals_Times_Ann 
   ; bs_times_id_is_plus_ann_d   := Certify_Not_Times_Id_Equals_Plus_Ann 
   ; bs_left_left_absorptive_d   := Certify_Not_Left_Left_Absorptive (0, 1) 
   ; bs_left_right_absorptive_d  := Certify_Not_Left_Right_Absorptive (0, 1) 
   ; bs_right_left_absorptive_d  := Certify_Not_Right_Left_Absorptive (0, 1) 
   ; bs_right_right_absorptive_d := Certify_Not_Right_Right_Absorptive (0, 1) 
  |}. 


Definition bs_max_plus : bs (S := nat) := 
{|
  bs_eqv          := eqv_eq_nat 
; bs_plus         := bop_max
; bs_times        := bop_plus
; bs_plus_certs  := sg_certs_max
; bs_times_certs := sg_certs_plus
; bs_certs       := bs_certs_max_plus
; bs_ast          := Ast_bs_max_plus
|}.

