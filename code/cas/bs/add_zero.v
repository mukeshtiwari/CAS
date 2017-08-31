
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

Require Import CAS.code.cas.eqv.add_constant.
Require Import CAS.code.cas.sg.add_ann.
Require Import CAS.code.cas.sg.add_id.

Definition bops_add_zero_left_distributive_check : 
   ∀ {S : Type},  
     check_left_distributive (S := S) -> 
     check_left_distributive (S := (with_constant S)) 
:= λ {S} dS,  
   match dS with 
   | Certify_Left_Distributive => Certify_Left_Distributive (S := (with_constant S)) 
   | Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive (S := (with_constant S)) (inr s1, (inr s2, inr _ s3))
   end. 

Definition bops_add_zero_right_distributive_check : 
   ∀ {S : Type},  
     check_right_distributive (S := S) -> 
     check_right_distributive (S := (with_constant S)) 
:= λ {S} dS,  
   match dS with 
   | Certify_Right_Distributive => Certify_Right_Distributive (S := (with_constant S)) 
   | Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive (S := (with_constant S)) (inr _ s1, (inr _ s2, inr _ s3))
   end. 

Definition bops_add_zero_left_left_absorptive_check : 
   ∀ {S : Type} (s : S), 
     check_left_left_absorptive (S := S) -> 
     check_left_left_absorptive (S := (with_constant S))
:= λ {S} s dS ,  
match dS with 
| Certify_Left_Left_Absorptive => Certify_Left_Left_Absorptive (S := (with_constant S))
| Certify_Not_Left_Left_Absorptive (s1, s2) => 
     Certify_Not_Left_Left_Absorptive (S := (with_constant S)) (inr _ s1, inr _ s2)
end. 


Definition bops_add_zero_left_right_absorptive_check : 
   ∀ {S : Type} (s : S), 
     check_left_right_absorptive (S := S) -> 
     check_left_right_absorptive (S := (with_constant S))
:= λ {S} s dS ,  
match dS with 
| Certify_Left_Right_Absorptive => Certify_Left_Right_Absorptive (S := (with_constant S))
| Certify_Not_Left_Right_Absorptive (s1, s2) => 
     Certify_Not_Left_Right_Absorptive (S := (with_constant S)) (inr _ s1, inr _ s2)
end. 

Definition bops_add_zero_right_left_absorptive_check : 
   ∀ {S : Type} (s : S), 
     check_right_left_absorptive (S := S) -> 
     check_right_left_absorptive (S := (with_constant S))
:= λ {S} s dS ,  
match dS with 
| Certify_Right_Left_Absorptive => Certify_Right_Left_Absorptive (S := (with_constant S))
| Certify_Not_Right_Left_Absorptive (s1, s2) => 
     Certify_Not_Right_Left_Absorptive (S := (with_constant S)) (inr _ s1, inr _ s2)
end. 

Definition bops_add_zero_right_right_absorptive_check : 
   ∀ {S : Type} (s : S), 
     check_right_right_absorptive (S := S) -> 
     check_right_right_absorptive (S := (with_constant S))
:= λ {S} s dS ,  
match dS with 
| Certify_Right_Right_Absorptive => Certify_Right_Right_Absorptive (S := (with_constant S))
| Certify_Not_Right_Right_Absorptive (s1, s2) => 
     Certify_Not_Right_Right_Absorptive (S := (with_constant S)) (inr _ s1, inr _ s2)
end. 

Definition bs_certs_add_zero : 
  ∀ {S : Type}, eqv_certificates (S := S) -> bs_certificates (S := S) -> bs_certificates (S := (with_constant S))
:= λ {S} eqvS pS, 
match certify_nontrivial_witness (eqv_nontrivial eqvS) with 
| Certify_Witness s =>  
{|
  bs_left_distributive_d    := 
     bops_add_zero_left_distributive_check (bs_left_distributive_d pS) 
; bs_right_distributive_d   := 
     bops_add_zero_right_distributive_check (bs_right_distributive_d pS) 

; bs_left_left_absorptive_d      := 
     bops_add_zero_left_left_absorptive_check s (bs_left_left_absorptive_d pS)
; bs_left_right_absorptive_d      := 
     bops_add_zero_left_right_absorptive_check s (bs_left_right_absorptive_d pS)
; bs_right_left_absorptive_d     := 
     bops_add_zero_right_left_absorptive_check s (bs_right_left_absorptive_d pS)
; bs_right_right_absorptive_d     := 
     bops_add_zero_right_right_absorptive_check s (bs_right_right_absorptive_d pS)

; bs_plus_id_is_times_ann_d :=  Certify_Plus_Id_Equals_Times_Ann  
; bs_times_id_is_plus_ann_d :=  
  match bs_times_id_is_plus_ann_d pS with (*** NB : type coer ***) 
  | Certify_Times_Id_Equals_Plus_Ann => Certify_Times_Id_Equals_Plus_Ann  
  | Certify_Not_Times_Id_Equals_Plus_Ann => Certify_Not_Times_Id_Equals_Plus_Ann  
  end 
|}
end. 


Definition bs_add_zero : ∀ {S : Type},  bs (S := S) -> cas_constant -> bs (S := (with_constant S)) 
:= λ {S} bsS c, 
{| 
     bs_eqv          := eqv_add_constant (bs_eqv bsS) c 
   ; bs_plus         := bop_add_id (bs_plus bsS) c
   ; bs_times        := bop_add_ann (bs_times bsS) c
   ; bs_plus_certs  := sg_certs_add_id c 
                                (eqv_certs (bs_eqv bsS)) 
                                (bs_plus_certs bsS) 
   ; bs_times_certs := sg_certs_add_ann c 
                                (eqv_certs (bs_eqv bsS)) 
                                (bs_times_certs bsS) 
   ; bs_certs       := bs_certs_add_zero 
                                (eqv_certs (bs_eqv bsS))  
                                (bs_certs bsS)
   ; bs_ast          := Ast_bs_add_zero (c, bs_ast bsS)
|}. 

