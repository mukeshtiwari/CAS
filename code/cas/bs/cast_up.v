Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.  
Require Import CAS.code.cef.  
Require Import CAS.code.ast.
Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records. 
Require Import CAS.code.eqv_records. 
Require Import CAS.code.bs_certificates.
Require Import CAS.code.bs_cert_records. 
Require Import CAS.code.bs_records. 
Require Import CAS.code.cas.sg.cast_up.


Definition bs_from_bs_C : ∀ {S : Type},  bs_C (S := S) -> bs (S := S)
:= λ {S} s, 
{| 
  bs_eqv          := bs_C_eqv s
; bs_plus         := bs_C_plus s
; bs_times        := bs_C_times s
; bs_plus_certs  := sg_certs_from_sg_C_certs 
                            (eqv_eq (bs_C_eqv s))
                            (bs_C_plus s)
                            (eqv_witness (bs_C_eqv s))
                            (eqv_new (bs_C_eqv s))                             
                            (bs_C_plus_certs s)  
; bs_times_certs := bs_C_times_certs s
; bs_certs       := bs_C_certs  s 
; bs_ast          := Ast_bs_from_bs_C (bs_C_ast s)
|}. 


Definition bs_from_bs_CS : ∀ {S : Type},  bs_CS (S := S) -> bs (S := S)
:= λ {S} s, 
{| 
  bs_eqv          := bs_CS_eqv s
; bs_plus         := bs_CS_plus s
; bs_times        := bs_CS_times s
; bs_plus_certs  := sg_certs_from_sg_CS_certs 
                      (eqv_eq  (bs_CS_eqv s))
                      (bs_CS_plus s)                      
                      (eqv_witness (bs_CS_eqv s))
                      (eqv_new (bs_CS_eqv s))                             
                      (bs_CS_plus_certs s)  
; bs_times_certs := bs_CS_times_certs s
; bs_certs       := bs_CS_certs s 
; bs_ast         := Ast_bs_from_bs_CS (bs_CS_ast s)
|}.

(* needs verification *) 
Definition bs_certs_from_semiring_certs : ∀ {S : Type},  @semiring_certificates S -> @bs_certificates S
:= λ {S} s,                                                                                                       
{|
  bs_left_distributive_d      := @Certify_Left_Distributive S
; bs_right_distributive_d     := @Certify_Right_Distributive S
; bs_plus_id_is_times_ann_d   := @semiring_plus_id_is_times_ann_d S s
; bs_times_id_is_plus_ann_d   := @semiring_times_id_is_plus_ann_d S s
; bs_left_left_absorptive_d   := @semiring_left_left_absorptive_d S s
; bs_left_right_absorptive_d  := @semiring_left_right_absorptive_d S s
; bs_right_left_absorptive_d  := match @semiring_left_left_absorptive_d S s with
                                 | Certify_Left_Left_Absorptive => @Certify_Right_Left_Absorptive S
                                 | Certify_Not_Left_Left_Absorptive p => @Certify_Not_Right_Left_Absorptive S p
                                 end 
; bs_right_right_absorptive_d := match @semiring_left_right_absorptive_d S s with
                                 | Certify_Left_Right_Absorptive => @Certify_Right_Right_Absorptive S
                                 | Certify_Not_Left_Right_Absorptive p => @Certify_Not_Right_Right_Absorptive S p
                                 end 
|}. 


Definition bs_C_from_semiring : ∀ {S : Type},  @semiring S -> @bs_C S
:= λ {S} s, 
{| 
  bs_C_eqv          := @semiring_eqv S s
; bs_C_plus         := @semiring_plus S s
; bs_C_times        := @semiring_times S s
; bs_C_plus_certs  :=  @semiring_plus_certs S s
; bs_C_times_certs := @semiring_times_certs S s
; bs_C_certs       := @bs_certs_from_semiring_certs S (semiring_certs s) 
; bs_C_ast         := Ast_bs_C_from_semiring (semiring_ast s)
|}. 


