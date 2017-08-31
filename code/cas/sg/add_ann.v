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


Definition bop_add_ann_commutative_check : 
   ∀ {S : Type},  @check_commutative S → @check_commutative (with_constant S) 
:= λ {S} dS,  
   match dS with 
   | Certify_Commutative            => Certify_Commutative
   | Certify_Not_Commutative (s, t) => Certify_Not_Commutative (inr _ s, inr _ t)
   end. 

Definition bop_add_ann_selective_check : 
   ∀ {S : Type},  @check_selective S → @check_selective (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Selective            => Certify_Selective 
   | Certify_Not_Selective (s, t) => Certify_Not_Selective (inr _ s, inr _ t)
   end. 

Definition bop_add_ann_idempotent_check : 
   ∀ {S : Type},  @check_idempotent S → @check_idempotent (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Idempotent     => Certify_Idempotent 
   | Certify_Not_Idempotent s => Certify_Not_Idempotent (inr _ s) 
   end. 

Definition bop_add_ann_exists_id_check : 
   ∀ {S : Type},  @check_exists_id S → @check_exists_id (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Exists_Id i   => Certify_Exists_Id (inr i)
   | Certify_Not_Exists_Id => Certify_Not_Exists_Id
   end. 

Definition bop_add_ann_not_is_left_check : 
   ∀ {S : Type},  @cas_constant -> @certify_witness S → @check_is_left (with_constant S)
:= λ {S} c dS,  
   match dS with 
   | Certify_Witness s => Certify_Not_Is_Left (inr _ s, inl _ c) 
   end. 

Definition bop_add_ann_not_is_left_assert : 
   ∀ {S : Type},  cas_constant -> @certify_witness S → @assert_not_is_left (with_constant S)
:= λ {S} c dS,  
   match dS with 
   | Certify_Witness s => Assert_Not_Is_Left (inr _ s, inl _ c) 
   end. 

Definition bop_add_ann_not_is_right_check : 
   ∀ {S : Type},  cas_constant -> @certify_witness S → @check_is_right (with_constant S)
:= λ {S} c dS,  
   match dS with 
   | Certify_Witness s => Certify_Not_Is_Right  (inl _ c, inr _ s) 
   end. 

Definition bop_add_ann_not_is_right_assert : 
   ∀ {S : Type},  cas_constant -> @certify_witness S → @assert_not_is_right (with_constant S)
:= λ {S} c dS,  
   match dS with 
   | Certify_Witness s => Assert_Not_Is_Right (inl _ c, inr _ s) 
   end. 



Definition sg_certs_add_ann : ∀ {S : Type},  cas_constant -> @eqv_certificates S -> @sg_certificates S -> @sg_certificates (with_constant S)
:= λ {S} c eqvS sgS,  
match certify_nontrivial_witness (eqv_nontrivial eqvS), 
      certify_nontrivial_negate (eqv_nontrivial eqvS) 
with 
| Certify_Witness s, Certify_Negate f =>  
{|
  sg_associative      := Assert_Associative  
; sg_congruence       := Assert_Bop_Congruence  
; sg_commutative_d    := bop_add_ann_commutative_check (sg_commutative_d sgS) 
; sg_selective_d      := bop_add_ann_selective_check (sg_selective_d sgS) 
; sg_is_left_d        := bop_add_ann_not_is_left_check c (certify_nontrivial_witness (eqv_nontrivial eqvS))
; sg_is_right_d       := bop_add_ann_not_is_right_check c (certify_nontrivial_witness (eqv_nontrivial eqvS))
; sg_idempotent_d     := bop_add_ann_idempotent_check (sg_idempotent_d sgS) 
; sg_exists_id_d      := bop_add_ann_exists_id_check (sg_exists_id_d sgS)
; sg_exists_ann_d     := Certify_Exists_Ann  (inl c) 
; sg_left_cancel_d    := Certify_Not_Left_Cancellative  (inl c, (inr s, inr (f s))) 
; sg_right_cancel_d   := Certify_Not_Right_Cancellative  (inl c, (inr s, inr (f s))) 
; sg_left_constant_d  := Certify_Not_Left_Constant  (inr s, (inr s, inl c))
; sg_right_constant_d := Certify_Not_Right_Constant  (inr s, (inr s, inl c))
; sg_anti_left_d      := Certify_Not_Anti_Left  (inl c, inr s) 
; sg_anti_right_d     := Certify_Not_Anti_Right  (inl c, inr s) 
|}
end. 

Definition sg_C_certs_add_ann : ∀ {S : Type},  cas_constant -> eqv_certificates (S := S) -> sg_C_certificates (S := S) -> sg_C_certificates (S := (with_constant S)) 
:= λ {S} c eqvS sgS,  
match certify_nontrivial_witness (eqv_nontrivial eqvS), 
      certify_nontrivial_negate (eqv_nontrivial eqvS) 
with 
| Certify_Witness s, Certify_Negate f =>  
{|
  sg_C_associative   := Assert_Associative  
; sg_C_congruence    := Assert_Bop_Congruence  
; sg_C_commutative   := Assert_Commutative  
; sg_C_selective_d   := bop_add_ann_selective_check (sg_C_selective_d sgS) 
; sg_C_idempotent_d  := bop_add_ann_idempotent_check (sg_C_idempotent_d sgS) 
; sg_C_exists_id_d   := bop_add_ann_exists_id_check (sg_C_exists_id_d sgS)
; sg_C_exists_ann_d  := Certify_Exists_Ann  (inl c) 
; sg_C_left_cancel_d  := Certify_Not_Left_Cancellative  (inl c, (inr s, inr (f s))) 
; sg_C_right_cancel_d := Certify_Not_Right_Cancellative  (inl c, (inr s, inr (f s))) 
; sg_C_left_constant_d  := Certify_Not_Left_Constant  (inr s, (inr s, inl c))
; sg_C_right_constant_d := Certify_Not_Right_Constant  (inr s, (inr s, inl c))
; sg_C_anti_left_d      := Certify_Not_Anti_Left  (inl c, inr s) 
; sg_C_anti_right_d     := Certify_Not_Anti_Right  (inl c, inr s) 
|}
end. 


Definition sg_CI_certs_add_ann : ∀ {S : Type},  cas_constant -> eqv_certificates (S := S) -> sg_CI_certificates (S := S) -> sg_CI_certificates (S := (with_constant S)) 
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
; sg_CI_selective_d        := bop_add_ann_selective_check (sg_CI_selective_d sgS) 
; sg_CI_exists_id_d        := bop_add_ann_exists_id_check (sg_CI_exists_id_d sgS)
; sg_CI_exists_ann_d       := Certify_Exists_Ann  (inl S c) 
|}
end. 


Definition sg_CS_certs_add_ann : ∀ {S : Type},  cas_constant -> eqv_certificates (S := S) -> sg_CS_certificates (S := S) -> sg_CS_certificates (S := with_constant S) 
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
; sg_CS_exists_id_d   := bop_add_ann_exists_id_check (sg_CS_exists_id_d sg)
; sg_CS_exists_ann_d  := Certify_Exists_Ann  (inl c) 
|}
end. 


Definition sg_add_ann:  ∀ {S : Type},  cas_constant -> sg (S := S) -> sg (S := (with_constant S)) 
:= λ {S} c sgS, 
   {| 
     sg_eq     := eqv_add_constant (sg_eq sgS) c 
   ; sg_bop    := bop_add_ann (sg_bop sgS) c
   ; sg_certs  := sg_certs_add_ann c (eqv_certs (sg_eq sgS)) (sg_certs sgS) 
   ; sg_ast    := Ast_sg_add_ann (c, sg_ast sgS)
   |}. 

Definition sg_C_add_ann : ∀ {S : Type} (c : cas_constant),  sg_C (S := S) -> sg_C (S := (with_constant S)) 
:= λ {S} c sgS, 
   {| 
     sg_C_eqv       := eqv_add_constant (sg_C_eqv sgS) c  
   ; sg_C_bop       := bop_add_ann (sg_C_bop sgS) c 
   ; sg_C_certs     := sg_C_certs_add_ann c (eqv_certs (sg_C_eqv sgS)) (sg_C_certs sgS) 
   ; sg_C_ast       := Ast_sg_C_add_ann (c, sg_C_ast sgS)
   |}. 

Definition sg_CI_add_ann : ∀ {S : Type} (c : cas_constant),  sg_CI (S := S) -> sg_CI (S := (with_constant S)) 
:= λ {S} c sgS, 
   {| 
     sg_CI_eqv       := eqv_add_constant (sg_CI_eqv sgS) c  
   ; sg_CI_bop       := bop_add_ann (sg_CI_bop sgS) c 
   ; sg_CI_certs    := sg_CI_certs_add_ann c (eqv_certs (sg_CI_eqv sgS)) (sg_CI_certs sgS) 
   ; sg_CI_ast       := Ast_sg_CI_add_ann (c, sg_CI_ast sgS)
   |}. 

Definition sg_CS_add_ann : ∀ {S : Type} (c : cas_constant),  sg_CS (S := S) -> sg_CS (S := (with_constant S)) 
:= λ {S} c sgS, 
   {| 
     sg_CS_eqv       := eqv_add_constant (sg_CS_eqv sgS) c  
   ; sg_CS_bop       := bop_add_ann (sg_CS_bop sgS) c 
   ; sg_CS_certs    := sg_CS_certs_add_ann c (eqv_certs (sg_CS_eqv sgS)) (sg_CS_certs sgS) 
   ; sg_CS_ast       := Ast_sg_CS_add_ann (c, sg_CS_ast sgS)
   |}. 

