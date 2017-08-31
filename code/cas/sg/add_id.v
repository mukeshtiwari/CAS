Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.data.
Require Import CAS.code.brel.
Require Import CAS.code.bop.

Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.eqv_records.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.sg_records.

Require Import CAS.code.cas.eqv.add_constant. 

Definition bop_add_id_commutative_check : 
   ∀ {S : Type},  check_commutative (S := S) → check_commutative (S := (with_constant S)) 
:= λ {S} dS,  
   match dS with 
   | Certify_Commutative            => Certify_Commutative (S := (with_constant S)) 
   | Certify_Not_Commutative (s, t) => 
        Certify_Not_Commutative (S := (with_constant S)) (inr _ s, inr _ t)
   end. 

Definition bop_add_id_selective_check : 
   ∀ {S : Type},  check_selective (S := S) → check_selective (S := (with_constant S)) 
:= λ {S} dS,  
   match dS with 
   | Certify_Selective            => Certify_Selective(S := (with_constant S)) 
   | Certify_Not_Selective (s, t) => 
        Certify_Not_Selective (S := (with_constant S)) (inr _ s, inr _ t)
   end. 

Definition bop_add_id_idempotent_check : 
   ∀ {S : Type},  check_idempotent (S := S) → check_idempotent (S := (with_constant S)) 
:= λ {S} dS,  
   match dS with 
   | Certify_Idempotent       => Certify_Idempotent (S := (with_constant S)) 
   | Certify_Not_Idempotent s => Certify_Not_Idempotent (S := (with_constant S)) (inr _ s) 
   end. 


Definition bop_add_id_exists_ann_check : 
   ∀ {S : Type},  check_exists_ann (S := S) → check_exists_ann (S := (with_constant S)) 
:= λ {S} dS,  
   match dS with 
   | Certify_Exists_Ann a    => Certify_Exists_Ann (S := (with_constant S)) (inr _ a)
   | Certify_Not_Exists_Ann => Certify_Not_Exists_Ann (S := (with_constant S)) 
   end. 

Definition bop_add_id_not_is_left_check : 
   ∀ {S : Type},  cas_constant -> certify_witness (S := S) → check_is_left (S := (with_constant S)) 
:= λ {S} c dS,  
   match dS with 
   | Certify_Witness s => Certify_Not_Is_Left (S := (with_constant S)) (inl _ c, inr _ s)
   end. 

Definition bop_add_id_not_is_left_assert : 
   ∀ {S : Type},  cas_constant -> certify_witness (S := S) → assert_not_is_left (S := (with_constant S)) 
:= λ {S} c dS,  
   match dS with 
   | Certify_Witness s => Assert_Not_Is_Left (S := (with_constant S)) (inl _ c, inr _ s)
   end. 


Definition bop_add_id_not_is_right_check : 
   ∀ {S : Type},  cas_constant -> certify_witness (S := S) → check_is_right (S := (with_constant S)) 
:= λ {S} c dS,  
   match dS with 
   | Certify_Witness s => Certify_Not_Is_Right (S := (with_constant S)) (inr _ s, inl _ c) 
   end. 

Definition bop_add_id_not_is_right_assert : 
   ∀ {S : Type},  cas_constant -> certify_witness (S := S) → assert_not_is_right (S := (with_constant S)) 
:= λ {S} c dS,  
   match dS with 
   | Certify_Witness s => Assert_Not_Is_Right (S := (with_constant S)) (inr _ s, inl _ c) 
   end. 


Definition bop_add_id_left_cancellative_check : 
   ∀ {S : Type} (c : cas_constant),
     check_anti_left (S := S) -> 
     check_left_cancellative (S := S) -> 
        check_left_cancellative (S := (with_constant S)) 
:= λ {S} c ad lcd,  
   match ad with 
   | Certify_Anti_Left => 
        match lcd with 
        | Certify_Left_Cancellative     => Certify_Left_Cancellative (S := (with_constant S)) 
        | Certify_Not_Left_Cancellative (s1, (s2, s3)) => 
             Certify_Not_Left_Cancellative (S := (with_constant S)) (inr s1, (inr s2, inr s3))
        end 
   | Certify_Not_Anti_Left (s1, s2) => 
        Certify_Not_Left_Cancellative (S := (with_constant S)) (inr s1, (inr s2, inl c)) 
   end. 


Definition bop_add_id_right_cancellative_check : 
   ∀ {S : Type} (c : cas_constant),
     check_anti_right (S := S) -> 
     check_right_cancellative (S := S) -> 
        check_right_cancellative (S := (with_constant S)) 
:= λ {S} c ad lcd,  
   match ad with 
   | Certify_Anti_Right => 
        match lcd with 
        | Certify_Right_Cancellative      => Certify_Right_Cancellative (S := (with_constant S)) 
        | Certify_Not_Right_Cancellative (s1, (s2, s3)) => 
             Certify_Not_Right_Cancellative (S := (with_constant S)) (inr s1, (inr s2, inr s3)) 
        end 
   | Certify_Not_Anti_Right (s1, s2) => 
        Certify_Not_Right_Cancellative (S := (with_constant S)) (inr s1, (inr s2, inl c))
   end. 

Definition sg_certs_add_id : ∀ {S : Type},  cas_constant -> eqv_certificates (S := S) -> sg_certificates (S := S) -> sg_certificates (S := (with_constant S)) 
:= λ {S} c eqvS sgS,  
match certify_nontrivial_witness (eqv_nontrivial eqvS), 
      certify_nontrivial_negate (eqv_nontrivial eqvS) 
with 
| Certify_Witness s, Certify_Negate f =>  
{|
  sg_associative      := Assert_Associative 
; sg_congruence       := Assert_Bop_Congruence  
; sg_commutative_d    := bop_add_id_commutative_check (sg_commutative_d sgS) 
; sg_selective_d      := bop_add_id_selective_check (sg_selective_d sgS) 
; sg_is_left_d        := bop_add_id_not_is_left_check c 
                            (certify_nontrivial_witness (eqv_nontrivial eqvS))
; sg_is_right_d       := bop_add_id_not_is_right_check c 
                            (certify_nontrivial_witness (eqv_nontrivial eqvS))
; sg_idempotent_d     := bop_add_id_idempotent_check (sg_idempotent_d sgS) 
; sg_exists_id_d      := Certify_Exists_Id  (inl c) 
; sg_exists_ann_d     := bop_add_id_exists_ann_check (sg_exists_ann_d sgS) 
; sg_left_cancel_d    := bop_add_id_left_cancellative_check c 
                            (sg_anti_left_d sgS)
                            (sg_left_cancel_d sgS)
; sg_right_cancel_d   := bop_add_id_right_cancellative_check c 
                            (sg_anti_right_d sgS)
                            (sg_right_cancel_d sgS)
; sg_left_constant_d  := Certify_Not_Left_Constant  (inl c, (inr s, inr (f s)))
; sg_right_constant_d := Certify_Not_Right_Constant (inl c, (inr s, inr (f s)))
; sg_anti_left_d      := Certify_Not_Anti_Left  (inr s, inl c)
; sg_anti_right_d     := Certify_Not_Anti_Right  (inr s, inl c)
|}
end. 


Definition sg_C_certs_add_id : ∀ {S : Type},  cas_constant -> eqv_certificates (S := S) -> sg_C_certificates (S := S) -> sg_C_certificates (S := (with_constant S))
:= λ {S} c eqvS sgS,  
match certify_nontrivial_witness (eqv_nontrivial eqvS), 
      certify_nontrivial_negate (eqv_nontrivial eqvS) 
with 
| Certify_Witness s, Certify_Negate f =>  
{|
  sg_C_associative   := Assert_Associative  
; sg_C_congruence    := Assert_Bop_Congruence  
; sg_C_commutative   := Assert_Commutative  
; sg_C_selective_d   := bop_add_id_selective_check (sg_C_selective_d sgS) 
; sg_C_idempotent_d  := bop_add_id_idempotent_check (sg_C_idempotent_d sgS) 
; sg_C_exists_id_d   := Certify_Exists_Id  (inl c) 
; sg_C_exists_ann_d  := bop_add_id_exists_ann_check (sg_C_exists_ann_d sgS) 
; sg_C_left_cancel_d    := bop_add_id_left_cancellative_check c 
                            (sg_C_anti_left_d sgS)
                            (sg_C_left_cancel_d sgS)
; sg_C_right_cancel_d   := bop_add_id_right_cancellative_check c 
                            (sg_C_anti_right_d sgS)
                            (sg_C_right_cancel_d sgS)
; sg_C_left_constant_d  := Certify_Not_Left_Constant  (inl c, (inr s, inr (f s)))
; sg_C_right_constant_d := Certify_Not_Right_Constant  (inl c, (inr s, inr (f s)))
; sg_C_anti_left_d      := Certify_Not_Anti_Left  (inr s, inl c)
; sg_C_anti_right_d     := Certify_Not_Anti_Right  (inr s, inl c)
|}
end. 

Definition sg_CI_certs_add_id : ∀ {S : Type},  cas_constant -> eqv_certificates (S := S) -> sg_CI_certificates (S := S) -> sg_CI_certificates (S := (with_constant S)) 
:= λ {S} c eqvS sgS,  
let wS := certify_nontrivial_witness (eqv_nontrivial eqvS) in 
match wS, certify_nontrivial_negate (eqv_nontrivial eqvS) 
with 
| Certify_Witness s, Certify_Negate f =>  
{|
  sg_CI_associative        := Assert_Associative  
; sg_CI_congruence         := Assert_Bop_Congruence  
; sg_CI_commutative        := Assert_Commutative  
; sg_CI_idempotent         := Assert_Idempotent  
; sg_CI_selective_d        := bop_add_id_selective_check (sg_CI_selective_d sgS) 
; sg_CI_exists_id_d        := Certify_Exists_Id  (inl c) 
; sg_CI_exists_ann_d       := bop_add_id_exists_ann_check (sg_CI_exists_ann_d sgS) 
|}
end. 


Definition sg_CS_certs_add_id : ∀ {S : Type},  cas_constant -> eqv_certificates (S := S) -> sg_CS_certificates (S := S) -> sg_CS_certificates (S := (with_constant S)) 
:= λ {S} c eqvS sg,  
let wS := certify_nontrivial_witness (eqv_nontrivial eqvS) in 
match wS, certify_nontrivial_negate (eqv_nontrivial eqvS) 
with 
| Certify_Witness s, Certify_Negate f =>  
{|
  sg_CS_associative   := Assert_Associative  
; sg_CS_congruence    := Assert_Bop_Congruence  
; sg_CS_commutative   := Assert_Commutative  
; sg_CS_selective     := Assert_Selective  
; sg_CS_exists_id_d   := Certify_Exists_Id  (inl c) 
; sg_CS_exists_ann_d  := bop_add_id_exists_ann_check (sg_CS_exists_ann_d sg) 
|}
end. 

Definition sg_add_id: ∀ {S : Type},  cas_constant -> sg (S := S) -> sg (S := (with_constant S))
:= λ {S} c sgS, 
   {| 
     sg_eq     := eqv_add_constant (sg_eq sgS) c 
   ; sg_bop    := bop_add_id (sg_bop sgS) c
   ; sg_certs  := sg_certs_add_id c (eqv_certs (sg_eq sgS)) (sg_certs sgS) 
   ; sg_ast    := Ast_sg_add_id (c, sg_ast sgS)
   |}. 

Definition sg_C_add_id : ∀ {S : Type} (c : cas_constant),  sg_C (S := S) -> sg_C (S := (with_constant S)) 
:= λ {S} c sgS, 
   {| 
     sg_C_eqv       := eqv_add_constant (sg_C_eqv sgS) c  
   ; sg_C_bop       := bop_add_id (sg_C_bop sgS) c 
   ; sg_C_certs     := sg_C_certs_add_id c (eqv_certs (sg_C_eqv sgS)) (sg_C_certs sgS) 
   ; sg_C_ast       := Ast_sg_C_add_id (c, sg_C_ast sgS)
   |}. 

Definition sg_CI_add_id : ∀ {S : Type} (c : cas_constant), sg_CI (S := S) -> sg_CI (S := (with_constant S)) 
:= λ {S} c sgS, 
   {| 
     sg_CI_eqv       := eqv_add_constant (sg_CI_eqv sgS) c  
   ; sg_CI_bop       := bop_add_id (sg_CI_bop sgS) c 
   ; sg_CI_certs    := sg_CI_certs_add_id c (eqv_certs (sg_CI_eqv sgS)) (sg_CI_certs sgS) 
   ; sg_CI_ast       := Ast_sg_CI_add_id (c, sg_CI_ast sgS)
   |}. 


Definition sg_CS_add_id : ∀ {S : Type} (c : cas_constant),  sg_CS (S := S) -> sg_CS (S := (with_constant S)) 
:= λ {S} c sgS, 
   {| 
     sg_CS_eqv       := eqv_add_constant (sg_CS_eqv sgS) c  
   ; sg_CS_bop       := bop_add_id (sg_CS_bop sgS) c 
   ; sg_CS_certs    := sg_CS_certs_add_id c (eqv_certs (sg_CS_eqv sgS)) (sg_CS_certs sgS) 
   ; sg_CS_ast       := Ast_sg_CS_add_id (c, sg_CS_ast sgS)
   |}. 

