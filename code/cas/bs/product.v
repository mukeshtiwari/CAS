
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

Require Import CAS.code.cas.eqv.product.
Require Import CAS.code.cas.sg.product. 



Definition bop_product_left_distributive_check : 
   ∀ {S T : Type},  
     assert_nontrivial (S := S) -> 
     assert_nontrivial (S := T) -> 
     check_left_distributive (S := S) -> 
     check_left_distributive (S := T) -> 
     check_left_distributive (S := (S * T)) 
:= λ {S T} ntS ntT dS dT,  
match certify_nontrivial_witness ntS, certify_nontrivial_witness ntT with 
| Certify_Witness s, Certify_Witness t => 
   match dS with 
   | Certify_Left_Distributive => 
     match dT with 
     | Certify_Left_Distributive => Certify_Left_Distributive 
     | Certify_Not_Left_Distributive (t1, (t2, t3)) => 
          Certify_Not_Left_Distributive ((s, t1), ((s, t2), (s, t3))) 
     end 
   | Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive ((s1, t), ((s2, t), (s3, t)))
   end
end. 

Definition bop_product_right_distributive_check : 
   ∀ {S T : Type},  
     assert_nontrivial (S := S) -> 
     assert_nontrivial (S := T) -> 
     check_right_distributive (S := S) -> 
     check_right_distributive (S := T) -> 
     check_right_distributive (S := (S * T)) 
:= λ {S T} ntS ntT dS dT,  
match certify_nontrivial_witness ntS, certify_nontrivial_witness ntT with 
| Certify_Witness s, Certify_Witness t => 
   match dS with 
   | Certify_Right_Distributive => 
     match dT with 
     | Certify_Right_Distributive => Certify_Right_Distributive  
     | Certify_Not_Right_Distributive (t1, (t2, t3)) => 
          Certify_Not_Right_Distributive  ((s, t1), ((s, t2), (s, t3))) 
     end 
   | Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive  ((s1, t), ((s2, t), (s3, t)))
   end
end. 

Definition bop_product_plus_id_is_times_ann_check : 
   ∀ {S T : Type},  
     check_plus_id_equals_times_ann (S := S) -> 
     check_plus_id_equals_times_ann (S := T) -> 
     check_plus_id_equals_times_ann (S := (S * T)) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Plus_Id_Equals_Times_Ann => 
     match dT with 
     | Certify_Plus_Id_Equals_Times_Ann => Certify_Plus_Id_Equals_Times_Ann  
     | Certify_Not_Plus_Id_Equals_Times_Ann => 
          Certify_Not_Plus_Id_Equals_Times_Ann  
     end 
   | Certify_Not_Plus_Id_Equals_Times_Ann => 
        Certify_Not_Plus_Id_Equals_Times_Ann 
   end. 

Definition bop_product_times_id_equals_plus_ann_check : 
   ∀ {S T : Type},  
     check_times_id_equals_plus_ann (S := S) -> 
     check_times_id_equals_plus_ann (S := T) -> 
     check_times_id_equals_plus_ann (S := (S * T)) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Times_Id_Equals_Plus_Ann => 
     match dT with 
     | Certify_Times_Id_Equals_Plus_Ann => Certify_Times_Id_Equals_Plus_Ann  
     | Certify_Not_Times_Id_Equals_Plus_Ann => 
          Certify_Not_Times_Id_Equals_Plus_Ann  
     end 
   | Certify_Not_Times_Id_Equals_Plus_Ann => 
        Certify_Not_Times_Id_Equals_Plus_Ann 
   end. 



Definition bop_product_left_left_absorptive_check : 
   ∀ {S T : Type} (s : S) (t : T),  
     check_left_left_absorptive (S := S) -> 
     check_left_left_absorptive (S := T) -> 
     check_left_left_absorptive (S := (S * T)) 
:= λ {S T} s t dS dT,  
match dS with 
| Certify_Left_Left_Absorptive => 
     match dT with 
     | Certify_Left_Left_Absorptive => Certify_Left_Left_Absorptive  
     | Certify_Not_Left_Left_Absorptive (t1, t2) => 
          Certify_Not_Left_Left_Absorptive  ((s, t1), (s, t2))
     end 
| Certify_Not_Left_Left_Absorptive (s1, s2) => 
        Certify_Not_Left_Left_Absorptive  ((s1, t), (s2, t))
end. 

Definition bop_product_left_right_absorptive_check : 
   ∀ {S T : Type} (s : S) (t : T),  
     check_left_right_absorptive (S := S) -> 
     check_left_right_absorptive (S := T) -> 
     check_left_right_absorptive (S := (S * T)) 
:= λ {S T} s t dS dT,  
match dS with 
| Certify_Left_Right_Absorptive => 
     match dT with 
     | Certify_Left_Right_Absorptive => Certify_Left_Right_Absorptive  
     | Certify_Not_Left_Right_Absorptive (t1, t2) => 
          Certify_Not_Left_Right_Absorptive  ((s, t1), (s, t2))
     end 
| Certify_Not_Left_Right_Absorptive (s1, s2) => 
        Certify_Not_Left_Right_Absorptive  ((s1, t), (s2, t))
end. 

Definition bop_product_right_left_absorptive_check : 
   ∀ {S T : Type} (s : S) (t : T),  
     check_right_left_absorptive (S := S) -> 
     check_right_left_absorptive (S := T) -> 
     check_right_left_absorptive (S := (S * T)) 
:= λ {S T} s t dS dT,  
match dS with 
| Certify_Right_Left_Absorptive => 
     match dT with 
     | Certify_Right_Left_Absorptive => Certify_Right_Left_Absorptive  
     | Certify_Not_Right_Left_Absorptive (t1, t2) => 
          Certify_Not_Right_Left_Absorptive  ((s, t1), (s, t2))
     end 
| Certify_Not_Right_Left_Absorptive (s1, s2) => 
        Certify_Not_Right_Left_Absorptive  ((s1, t), (s2, t))
end. 

Definition bop_product_right_right_absorptive_check : 
   ∀ {S T : Type} (s : S) (t : T),  
     check_right_right_absorptive (S := S) -> 
     check_right_right_absorptive (S := T) -> 
     check_right_right_absorptive (S := (S * T)) 
:= λ {S T} s t dS dT,  
match dS with 
| Certify_Right_Right_Absorptive => 
     match dT with 
     | Certify_Right_Right_Absorptive => Certify_Right_Right_Absorptive  
     | Certify_Not_Right_Right_Absorptive (t1, t2) => 
          Certify_Not_Right_Right_Absorptive  ((s, t1), (s, t2))
     end 
| Certify_Not_Right_Right_Absorptive (s1, s2) => 
        Certify_Not_Right_Right_Absorptive  ((s1, t), (s2, t))
end. 



Definition bs_certs_product : 
  ∀ {S T : Type}, 
        eqv_certificates (S := S) -> eqv_certificates (S := T) -> bs_certificates (S := S) -> bs_certificates (S := T) -> bs_certificates (S := (S * T)) 
:= λ {S T} eqvS eqvT bsS bsT, 
match certify_nontrivial_witness  (eqv_nontrivial  eqvS), 
      certify_nontrivial_witness (eqv_nontrivial eqvT)
with 
| Certify_Witness s, Certify_Witness t => 
{|
  bs_left_distributive_d      := bop_product_left_distributive_check 
                                     (eqv_nontrivial eqvS)  
                                     (eqv_nontrivial eqvT)  
                                     (bs_left_distributive_d bsS)
                                     (bs_left_distributive_d bsT)
; bs_right_distributive_d     := bop_product_right_distributive_check 
                                     (eqv_nontrivial eqvS)  
                                     (eqv_nontrivial eqvT)  
                                     (bs_right_distributive_d bsS)
                                     (bs_right_distributive_d bsT)
; bs_plus_id_is_times_ann_d   := bop_product_plus_id_is_times_ann_check 
                                     (bs_plus_id_is_times_ann_d bsS)
                                     (bs_plus_id_is_times_ann_d bsT)
; bs_times_id_is_plus_ann_d   := bop_product_times_id_equals_plus_ann_check 
                                     (bs_times_id_is_plus_ann_d bsS)
                                     (bs_times_id_is_plus_ann_d bsT)
; bs_left_left_absorptive_d   := bop_product_left_left_absorptive_check s t 
                                     (bs_left_left_absorptive_d bsS)
                                     (bs_left_left_absorptive_d bsT)
; bs_left_right_absorptive_d  := bop_product_left_right_absorptive_check s t 
                                     (bs_left_right_absorptive_d bsS)
                                     (bs_left_right_absorptive_d bsT)
; bs_right_left_absorptive_d  := bop_product_right_left_absorptive_check s t
                                     (bs_right_left_absorptive_d bsS)
                                     (bs_right_left_absorptive_d bsT)
; bs_right_right_absorptive_d := bop_product_right_right_absorptive_check s t
                                     (bs_right_right_absorptive_d bsS)
                                     (bs_right_right_absorptive_d bsT)

|}
end. 

Definition bs_product : ∀ {S T : Type},  bs (S := S) -> bs (S := T) -> bs (S := (S * T)) 
:= λ {S T} bsS bsT, 
   {| 
     bs_eqv         := eqv_product (bs_eqv bsS) (bs_eqv bsT) 
   ; bs_plus        := bop_product (bs_plus bsS) (bs_plus bsT) 
   ; bs_times       := bop_product (bs_times bsS) (bs_times bsT) 
   ; bs_plus_certs  := sg_certs_product 
                           (eqv_certs (bs_eqv bsS))
                           (eqv_certs (bs_eqv bsT)) 
                           (bs_plus_certs bsS) 
                           (bs_plus_certs bsT) 
   ; bs_times_certs := sg_certs_product 
                           (eqv_certs (bs_eqv bsS))
                           (eqv_certs (bs_eqv bsT)) 
                           (bs_times_certs bsS) 
                           (bs_times_certs bsT) 
   ; bs_certs       := bs_certs_product 
                           (eqv_certs (bs_eqv bsS))
                           (eqv_certs (bs_eqv bsT)) 
                           (bs_certs bsS) 
                           (bs_certs bsT) 
   ; bs_ast         := Ast_bs_product(bs_ast bsS, bs_ast bsT)
   |}. 



