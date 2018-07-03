Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.
Require Import CAS.code.combined.
Require Import CAS.code.cef.

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
Require Import CAS.code.cas.sg.llex. 
Require Import CAS.code.cas.sg.product. 



(* 

C = Constructor 
P = Property 

  1) C_P_check 
  2) C_P_assert 
  3) C_not_P_assert 

*) 


Definition bops_llex_product_left_distributive_check 
     {S T : Type}
     (rS : brel S) 
     (rT : brel T) 
     (addS : binary_op S) 
     (addT mulT : binary_op T)
     (s : S) 
     (t : T) 
     (lcS_d : check_left_cancellative (S := S)) 
     (lkT_d : check_left_constant (S := T)) 
     (ldS_d : check_left_distributive (S := S)) 
     (ldT_d : check_left_distributive (S := T)) : 
     check_left_distributive (S := (S * T)) 
:= 
match ldS_d with 
| Certify_Left_Distributive => 
   match ldT_d with 
   | Certify_Left_Distributive => 
       match lcS_d with 
       | Certify_Left_Cancellative => Certify_Left_Distributive  
       | Certify_Not_Left_Cancellative (s1, (s2, s3)) => 
            match lkT_d with 
            | Certify_Left_Constant => Certify_Left_Distributive  
            | Certify_Not_Left_Constant (t1, (t2, t3)) => 
                  Certify_Not_Left_Distributive  
                     (cef_llex_product_not_left_distributive rS rT s1 s2 s3 t1 t2 t3
                         addS addT mulT) 
            end 
       end 
   | Certify_Not_Left_Distributive (t1, (t2, t3)) => 
          Certify_Not_Left_Distributive  ((s, t1), ((s, t2), (s, t3))) 
   end 
| Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive  ((s1, t), ((s2, t), (s3, t))) 
end.

Definition bops_llex_product_right_distributive_check 
     {S T : Type}
     (rS : brel S) 
     (rT : brel T) 
     (addS : binary_op S) 
     (addT mulT : binary_op T)
     (s : S) 
     (t : T) 
     (lcS_d : check_right_cancellative (S := S)) 
     (lkT_d : check_right_constant (S := T)) 
     (ldS_d : check_right_distributive (S := S)) 
     (ldT_d : check_right_distributive (S := T)) : 
     check_right_distributive (S := (S * T)) 
:= 
match ldS_d with 
| Certify_Right_Distributive => 
   match ldT_d with 
   | Certify_Right_Distributive => 
       match lcS_d with 
       | Certify_Right_Cancellative => Certify_Right_Distributive  
       | Certify_Not_Right_Cancellative (s1, (s2, s3)) => 
            match lkT_d with 
            | Certify_Right_Constant => Certify_Right_Distributive  
            | Certify_Not_Right_Constant (t1, (t2, t3)) => 
                  Certify_Not_Right_Distributive  
                     (cef_llex_product_not_right_distributive rS rT s1 s2 s3 t1 t2 t3
                         addS addT mulT) 

            end 
       end 
   | Certify_Not_Right_Distributive (t1, (t2, t3)) => 
          Certify_Not_Right_Distributive  ((s, t1), ((s, t2), (s, t3))) 
   end 
| Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive  ((s1, t), ((s2, t), (s3, t))) 
end.


(* these are the same as for product *) 
Definition bops_llex_product_plus_id_is_times_ann_check : 
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

Definition bops_llex_product_times_id_equals_plus_ann_check : 
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



Definition bops_llex_product_left_left_absorptive_check : 
   ∀ {S T : Type} (t : T),  
     check_left_left_absorptive (S := S) -> 
     check_left_left_absorptive (S := T) -> 
     check_anti_left (S := S) -> 
     check_left_left_absorptive (S := (S * T)) 
:= λ {S T} t dS dT alS,  
match dS with 
| Certify_Left_Left_Absorptive => 
     match dT with 
     | Certify_Left_Left_Absorptive => Certify_Left_Left_Absorptive  
     | Certify_Not_Left_Left_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Left => Certify_Left_Left_Absorptive  
       | Certify_Not_Anti_Left (s1, s2) => 
          Certify_Not_Left_Left_Absorptive  ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Left_Left_Absorptive (s1, s2) => 
        Certify_Not_Left_Left_Absorptive  ((s1, t), (s2, t))
end. 


Definition bops_llex_product_left_right_absorptive_check : 
   ∀ {S T : Type} (t : T),  
     check_left_right_absorptive (S := S) -> 
     check_left_right_absorptive (S := T) -> 
     check_anti_right (S := S) -> 
     check_left_right_absorptive (S := (S * T)) 
:= λ {S T} t dS dT alS,  
match dS with 
| Certify_Left_Right_Absorptive => 
     match dT with 
     | Certify_Left_Right_Absorptive => Certify_Left_Right_Absorptive  
     | Certify_Not_Left_Right_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Right => Certify_Left_Right_Absorptive  
       | Certify_Not_Anti_Right (s1, s2) => 
          Certify_Not_Left_Right_Absorptive  ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Left_Right_Absorptive (s1, s2) => 
        Certify_Not_Left_Right_Absorptive  ((s1, t), (s2, t))
end. 



Definition bops_llex_product_right_left_absorptive_check : 
   ∀ {S T : Type} (t : T),  
     check_right_left_absorptive (S := S) -> 
     check_right_left_absorptive (S := T) -> 
     check_anti_left (S := S) -> 
     check_right_left_absorptive (S := (S * T)) 
:= λ {S T} t dS dT alS,  
match dS with 
| Certify_Right_Left_Absorptive => 
     match dT with 
     | Certify_Right_Left_Absorptive => Certify_Right_Left_Absorptive  
     | Certify_Not_Right_Left_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Left => Certify_Right_Left_Absorptive  
       | Certify_Not_Anti_Left (s1, s2) => 
          Certify_Not_Right_Left_Absorptive  ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Right_Left_Absorptive (s1, s2) => 
        Certify_Not_Right_Left_Absorptive  ((s1, t), (s2, t))
end. 


Definition bops_llex_product_right_right_absorptive_check : 
   ∀ {S T : Type} (t : T),  
     check_right_right_absorptive (S := S) -> 
     check_right_right_absorptive (S := T) -> 
     check_anti_right (S := S) -> 
     check_right_right_absorptive (S := (S * T)) 
:= λ {S T} t dS dT alS,  
match dS with 
| Certify_Right_Right_Absorptive => 
     match dT with 
     | Certify_Right_Right_Absorptive => Certify_Right_Right_Absorptive  
     | Certify_Not_Right_Right_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Right => Certify_Right_Right_Absorptive  
       | Certify_Not_Anti_Right (s1, s2) => 
          Certify_Not_Right_Right_Absorptive  ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Right_Right_Absorptive (s1, s2) => 
        Certify_Not_Right_Right_Absorptive  ((s1, t), (s2, t))
end. 




Definition bs_certs_llex_product : 
  ∀ {S T: Type}
     (rS : brel S) 
     (rT : brel T) 
     (addS : binary_op S) 
     (addT mulT : binary_op T),
    S -> 
    T -> 
    sg_certificates (S := S)  → 
    sg_certificates (S := T) → 
    bs_certificates (S := S) -> 
    bs_certificates (S := T) -> bs_certificates (S := (S * T)) 
:= λ {S T} rS rT addS addT mulT s t sg_timesS sg_timesT bsS bsT, 
{|
  bs_left_distributive_d     := bops_llex_product_left_distributive_check 
                                     rS rT addS addT mulT s t
                                     (sg_left_cancel_d sg_timesS)
                                     (sg_left_constant_d sg_timesT) 
                                     (bs_left_distributive_d bsS)
                                     (bs_left_distributive_d bsT)
; bs_right_distributive_d    := bops_llex_product_right_distributive_check 
                                     rS rT addS addT mulT s t
                                     (sg_right_cancel_d sg_timesS)
                                     (sg_right_constant_d sg_timesT) 
                                     (bs_right_distributive_d bsS)
                                     (bs_right_distributive_d bsT)
; bs_plus_id_is_times_ann_d := bops_llex_product_plus_id_is_times_ann_check 
                                     (bs_plus_id_is_times_ann_d bsS)
                                     (bs_plus_id_is_times_ann_d bsT)
; bs_times_id_is_plus_ann_d := bops_llex_product_times_id_equals_plus_ann_check 
                                     (bs_times_id_is_plus_ann_d bsS)
                                     (bs_times_id_is_plus_ann_d bsT)
; bs_left_left_absorptive_d := bops_llex_product_left_left_absorptive_check t 
                                     (bs_left_left_absorptive_d bsS)
                                     (bs_left_left_absorptive_d bsT) 
                                     (sg_anti_left_d sg_timesS) 
; bs_left_right_absorptive_d := bops_llex_product_left_right_absorptive_check t 
                                     (bs_left_right_absorptive_d bsS)
                                     (bs_left_right_absorptive_d bsT) 
                                     (sg_anti_right_d sg_timesS)
; bs_right_left_absorptive_d := bops_llex_product_right_left_absorptive_check t 
                                     (bs_right_left_absorptive_d bsS)
                                     (bs_right_left_absorptive_d bsT) 
                                     (sg_anti_left_d sg_timesS)  
; bs_right_right_absorptive_d   := bops_llex_product_right_right_absorptive_check t
                                     (bs_right_right_absorptive_d bsS)
                                     (bs_right_right_absorptive_d bsT)
                                     (sg_anti_right_d sg_timesS) 

|}
.


Definition bs_C_llex_product : ∀ {S T : Type},  bs_CS (S := S) -> bs_C (S := T) -> bs_C (S := (S * T)) 
:= λ {S T} bsS bsT, 
{| 
     bs_C_eqv        := eqv_product  
                           (bs_CS_eqv bsS) 
                           (bs_C_eqv  bsT) 
   ; bs_C_plus       := bop_llex 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (bs_CS_plus bsS) 
                           (bs_C_plus bsT) 
   ; bs_C_times       := bop_product 
                           (bs_CS_times bsS) 
                           (bs_C_times bsT) 
   ; bs_C_plus_certs := sg_C_certs_llex 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (bs_CS_plus bsS) 
                           (eqv_witness (bs_CS_eqv bsS)) (eqv_new (bs_CS_eqv bsS)) 
                           (eqv_witness (bs_C_eqv bsT)) (eqv_new (bs_C_eqv bsT)) 
                           (bs_CS_plus_certs bsS) 
                           (bs_C_plus_certs bsT) 
   ; bs_C_times_certs := sg_certs_product 
                           (eqv_witness (bs_CS_eqv bsS)) 
                           (eqv_witness (bs_C_eqv bsT)) 
                           (bs_CS_times_certs bsS)
                           (bs_C_times_certs bsT)
   ; bs_C_certs    := bs_certs_llex_product 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (eqv_eq (bs_C_eqv bsT)) 
                           (bs_CS_plus bsS)
                           (bs_C_plus bsT) 
                           (bs_C_times bsT)  
                           (eqv_witness (bs_CS_eqv bsS)) 
                           (eqv_witness (bs_C_eqv bsT)) 
                           (bs_CS_times_certs bsS) 
                           (bs_C_times_certs bsT) 
                           (bs_CS_certs bsS) 
                           (bs_C_certs bsT) 
   ; bs_C_ast        := Ast_bs_C_llex (bs_CS_ast bsS, bs_C_ast bsT)
|}. 

Definition bs_CS_llex_product : ∀ {S T : Type},  bs_CS (S := S) -> bs_CS (S := T) -> bs_CS (S := (S * T)) 
:= λ {S T} bsS bsT, 
{| 
     bs_CS_eqv        := eqv_product  
                           (bs_CS_eqv bsS) 
                           (bs_CS_eqv bsT) 
   ; bs_CS_plus       := bop_llex 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (bs_CS_plus bsS) 
                           (bs_CS_plus bsT) 
   ; bs_CS_times       := bop_product 
                           (bs_CS_times bsS) 
                           (bs_CS_times bsT) 
   ; bs_CS_plus_certs := sg_CS_certs_llex 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (bs_CS_plus bsS) 
                           (bs_CS_plus_certs bsS) 
                           (bs_CS_plus_certs bsT) 
   ; bs_CS_times_certs := sg_certs_product 
                           (eqv_witness (bs_CS_eqv bsS)) 
                           (eqv_witness (bs_CS_eqv bsT)) 
                           (bs_CS_times_certs bsS)
                           (bs_CS_times_certs bsT)
   ; bs_CS_certs    := bs_certs_llex_product 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (eqv_eq (bs_CS_eqv bsT)) 
                           (bs_CS_plus bsS)
                           (bs_CS_plus bsT) 
                           (bs_CS_times bsT)  
                           (eqv_witness (bs_CS_eqv bsS)) 
                           (eqv_witness (bs_CS_eqv bsT)) 
                           (bs_CS_times_certs bsS) 
                           (bs_CS_times_certs bsT) 
                           (bs_CS_certs bsS) 
                           (bs_CS_certs bsT) 
   ; bs_CS_ast        := Ast_bs_CS_llex (bs_CS_ast bsS, bs_CS_ast bsT)
|}. 

