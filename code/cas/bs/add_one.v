Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.

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

Definition bops_add_one_left_distributive_check : 
   ∀ {S : Type} 
     (c : cas_constant),
     check_idempotent (S := S) -> 
     check_left_left_absorptive (S := S) -> 
     check_right_left_absorptive (S := S) -> 
     check_left_distributive (S := S) ->  check_left_distributive (S := (with_constant S))
:= λ {S} c idemS_d llaS_d rlaS_d ldS_d, 
   match ldS_d with 
   | Certify_Left_Distributive  => 
    match llaS_d with 
    | Certify_Left_Left_Absorptive => 
      match rlaS_d with 
      | Certify_Right_Left_Absorptive => 
         match idemS_d with 
         | Certify_Idempotent      => Certify_Left_Distributive 
         | Certify_Not_Idempotent s => Certify_Not_Left_Distributive (inr s, (inl c, inl c))
        end 
      | Certify_Not_Right_Left_Absorptive (s1, s2) => 
            Certify_Not_Left_Distributive (inr _ s1, (inr _ s2, inl _ c))
      end 
    | Certify_Not_Left_Left_Absorptive (s1, s2) => 
         Certify_Not_Left_Distributive (inr _ s1, (inl _ c, inr _ s2))
    end 
   | Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive (inr _ s1, (inr _ s2, inr _ s3))
   end. 


Definition bops_add_one_right_distributive_check : 
   ∀ {S : Type} 
     (c : cas_constant),
     check_idempotent (S := S) -> 
     check_left_right_absorptive (S := S) -> 
     check_right_right_absorptive (S := S) -> 
     check_right_distributive (S := S) ->  check_right_distributive (S := (with_constant S))
:= λ {S} c idemS_d llaS_d rlaS_d ldS_d, 
   match ldS_d with 
   | Certify_Right_Distributive => 
    match llaS_d with 
    | Certify_Left_Right_Absorptive => 
      match rlaS_d with 
      | Certify_Right_Right_Absorptive => 
         match idemS_d with 
         | Certify_Idempotent      => Certify_Right_Distributive 
         | Certify_Not_Idempotent s => Certify_Not_Right_Distributive (inr s, (inl c, inl c))
        end 
      | Certify_Not_Right_Right_Absorptive (s1, s2) => 
            Certify_Not_Right_Distributive (inr _ s1, (inr _ s2, inl _ c))
      end 
    | Certify_Not_Left_Right_Absorptive (s1, s2) => 
         Certify_Not_Right_Distributive (inr _ s1, (inl _ c, inr _ s2))
    end 
   | Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive (inr _ s1, (inr _ s2, inr _ s3))
   end. 


Definition bops_add_one_left_left_absorptive_check : 
   ∀ {S : Type} 
     (c : cas_constant),
     check_idempotent (S := S) -> 
     check_left_left_absorptive (S := S) -> check_left_left_absorptive (S := (with_constant S))
:= λ {S} c idemS_d laS_d, 
   match laS_d with 
   | Certify_Left_Left_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Left_Left_Absorptive 
     | Certify_Not_Idempotent s =>  Certify_Not_Left_Left_Absorptive (inr s, inl c) 
     end 
   | Certify_Not_Left_Left_Absorptive (s1, s2) => Certify_Not_Left_Left_Absorptive (inr _ s1, inr _ s2)
   end. 


Definition bops_add_one_left_right_absorptive_check : 
   ∀ {S : Type} 
     (c : cas_constant),
     check_idempotent (S := S) -> 
     check_left_right_absorptive (S := S) -> check_left_right_absorptive (S := (with_constant S))
:= λ {S} c idemS_d laS_d, 
   match laS_d with 
   | Certify_Left_Right_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Left_Right_Absorptive 
     | Certify_Not_Idempotent s =>  Certify_Not_Left_Right_Absorptive (inr s, inl c) 
     end 
   | Certify_Not_Left_Right_Absorptive (s1, s2) => Certify_Not_Left_Right_Absorptive (inr _ s1, inr _ s2)
   end. 


Definition bops_add_one_right_left_absorptive_check : 
   ∀ {S : Type} 
     (c : cas_constant),
     check_idempotent (S := S) -> 
     check_right_left_absorptive (S := S) -> check_right_left_absorptive (S := (with_constant S))
:= λ {S} c idemS_d laS_d, 
   match laS_d with 
   | Certify_Right_Left_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Right_Left_Absorptive 
     | Certify_Not_Idempotent s =>  Certify_Not_Right_Left_Absorptive (inr s, inl c) 
     end 
   | Certify_Not_Right_Left_Absorptive (s1, s2) => Certify_Not_Right_Left_Absorptive (inr _ s1, inr _ s2)
   end. 


Definition bops_add_one_right_right_absorptive_check : 
   ∀ {S : Type} 
     (c : cas_constant),
     check_idempotent (S := S) -> 
     check_right_right_absorptive (S := S) -> check_right_right_absorptive (S := (with_constant S))
:= λ {S} c idemS_d laS_d, 
   match laS_d with 
   | Certify_Right_Right_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Right_Right_Absorptive 
     | Certify_Not_Idempotent s =>  Certify_Not_Right_Right_Absorptive (inr s, inl c) 
     end 
   | Certify_Not_Right_Right_Absorptive (s1, s2) => Certify_Not_Right_Right_Absorptive (inr _ s1, inr _ s2)
   end. 


Definition bs_certs_add_one : 
  ∀ {S : Type} (c : cas_constant),
     eqv_certificates (S := S) -> sg_certificates (S := S) -> bs_certificates (S := S) -> bs_certificates (S := (with_constant S))
:= λ {S} c eqvS ppS pS, 
{|
  bs_left_distributive_d      :=  bops_add_one_left_distributive_check c 
                                      (sg_idempotent_d ppS) 
                                      (bs_left_left_absorptive_d pS) 
                                      (bs_right_left_absorptive_d pS) 
                                      (bs_left_distributive_d pS) 
; bs_right_distributive_d     := bops_add_one_right_distributive_check c 
                                      (sg_idempotent_d ppS) 
                                      (bs_left_right_absorptive_d pS) 
                                      (bs_right_right_absorptive_d pS) 
                                      (bs_right_distributive_d pS) 
; bs_left_left_absorptive_d   := bops_add_one_left_left_absorptive_check c 
                                      (sg_idempotent_d ppS) 
                                      (bs_left_left_absorptive_d pS) 
; bs_left_right_absorptive_d  := bops_add_one_left_right_absorptive_check c 
                                      (sg_idempotent_d ppS) 
                                      (bs_left_right_absorptive_d pS) 
; bs_right_left_absorptive_d  := bops_add_one_right_left_absorptive_check c 
                                      (sg_idempotent_d ppS) 
                                      (bs_right_left_absorptive_d pS) 
; bs_right_right_absorptive_d := bops_add_one_right_right_absorptive_check c 
                                      (sg_idempotent_d ppS) 
                                      (bs_right_right_absorptive_d pS) 
; bs_plus_id_is_times_ann_d := 
  match bs_plus_id_is_times_ann_d pS with (*** NB : type coer ***) 
  | Certify_Plus_Id_Equals_Times_Ann => Certify_Plus_Id_Equals_Times_Ann  
  | Certify_Not_Plus_Id_Equals_Times_Ann => Certify_Not_Plus_Id_Equals_Times_Ann  
  end 
; bs_times_id_is_plus_ann_d :=  Certify_Times_Id_Equals_Plus_Ann  

|}. 

Definition bs_add_one : ∀ {S : Type}, bs (S := S) -> cas_constant -> bs (S := (with_constant S)) 
:= λ {S} bsS c, 
{| 
     bs_eqv         := eqv_add_constant (bs_eqv bsS) c 
   ; bs_plus        := bop_add_ann (bs_plus bsS) c
   ; bs_times       := bop_add_id (bs_times bsS) c
   ; bs_plus_certs  := sg_certs_add_ann c
                                (eqv_certs (bs_eqv bsS)) 
                                (bs_plus_certs bsS) 
   ; bs_times_certs := sg_certs_add_id c
                                (eqv_certs (bs_eqv bsS)) 
                                (bs_times_certs bsS) 
   ; bs_certs       := bs_certs_add_one c
                                (eqv_certs (bs_eqv bsS)) 
                                (bs_plus_certs bsS) 
                                (bs_certs bsS)
   ; bs_ast         := Ast_bs_add_one (c, bs_ast bsS)
|}. 



