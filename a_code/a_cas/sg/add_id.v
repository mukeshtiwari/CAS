Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.bop.add_id.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cas.eqv.add_constant.
Require Import CAS.theory.facts. 

Check bop_add_id_congruence. 

Definition sg_proofs_add_id : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
     eqv_proofs S rS -> 
     sg_proofs S rS bS -> 
        sg_proofs (with_constant S) (brel_add_constant rS c) (bop_add_id bS c)
:= λ S rS c bS eqvS sgS, 
{|
  A_sg_associative   := bop_add_id_associative S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_associative _ _ _ sgS)
; A_sg_congruence    := bop_add_id_congruence S rS c bS 
                           (A_eqv_symmetric _ _ eqvS)
                           (A_sg_congruence _ _ _ sgS) 
; A_sg_commutative_d := bop_add_id_commutative_decide S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_commutative_d _ _ _ sgS)
; A_sg_selective_d   := bop_add_id_selective_decide S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_selective_d _ _ _ sgS)
; A_sg_is_left_d     := inr _ (bop_add_id_not_is_left S rS c bS 
                                (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_is_right_d    := inr _ (bop_add_id_not_is_right S rS c bS 
                                (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_idempotent_d  := bop_add_id_idempotent_decide S rS c bS 
                           (A_sg_idempotent_d _ _ _ sgS)
; A_sg_exists_id_d   := inl _ (bop_add_id_exists_id S rS c bS (A_eqv_reflexive _ _ eqvS))
; A_sg_exists_ann_d  := bop_add_id_exists_ann_decide S rS c bS 
                           (A_eqv_nontrivial _ _ eqvS)
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_exists_ann_d _ _ _ sgS) 
; A_sg_left_cancel_d    :=  bop_add_id_left_cancellative_decide S rS c bS 
                               (A_eqv_symmetric _ _ eqvS)
                               (A_sg_anti_left_d _ _ _ sgS) 
                               (A_sg_left_cancel_d _ _ _ sgS) 
; A_sg_right_cancel_d   := bop_add_id_right_cancellative_decide S rS c bS 
                               (A_eqv_symmetric _ _ eqvS)
                               (A_sg_anti_right_d _ _ _ sgS) 
                               (A_sg_right_cancel_d _ _ _ sgS) 
; A_sg_left_constant_d  := inr _ (bop_add_id_not_left_constant S rS c bS 
                                    (A_eqv_nontrivial _ _ eqvS)) 
; A_sg_right_constant_d := inr _ (bop_add_id_not_right_constant S rS c bS 
                                    (A_eqv_nontrivial _ _ eqvS)) 
; A_sg_anti_left_d      := inr _ (bop_add_id_not_anti_left S rS c bS
                                    (A_eqv_reflexive _ _ eqvS)
                                    (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_anti_right_d     := inr _ (bop_add_id_not_anti_right S rS c bS
                                    (A_eqv_reflexive _ _ eqvS)                                                            
                                    (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
|}. 



Definition sg_C_proofs_add_id : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
     eqv_proofs S rS -> 
     sg_C_proofs S rS bS -> 
        sg_C_proofs (with_constant S) (brel_add_constant rS c) (bop_add_id bS c)
:= λ S rS c bS eqvS sgS, 
{|
  A_sg_C_associative   := bop_add_id_associative S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_C_associative _ _ _ sgS)
; A_sg_C_congruence    := bop_add_id_congruence S rS c bS 
                           (A_eqv_symmetric _ _ eqvS)
                           (A_sg_C_congruence _ _ _ sgS) 
; A_sg_C_commutative   := bop_add_id_commutative S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_C_commutative _ _ _ sgS)
; A_sg_C_selective_d   := bop_add_id_selective_decide S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_C_selective_d _ _ _ sgS)
; A_sg_C_idempotent_d  := bop_add_id_idempotent_decide S rS c bS 
                           (A_sg_C_idempotent_d _ _ _ sgS)
; A_sg_C_exists_id_d   := inl _ (bop_add_id_exists_id S rS c bS (A_eqv_reflexive _ _ eqvS))
; A_sg_C_exists_ann_d  := bop_add_id_exists_ann_decide S rS c bS 
                           (A_eqv_nontrivial _ _ eqvS)
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_C_exists_ann_d _ _ _ sgS) 
; A_sg_C_left_cancel_d    := bop_add_id_left_cancellative_decide  S rS c bS 
                              (A_eqv_symmetric _ _ eqvS)
                              (A_sg_C_anti_left_d _ _ _ sgS) 
                              (A_sg_C_left_cancel_d _ _ _ sgS) 
; A_sg_C_right_cancel_d   := bop_add_id_right_cancellative_decide  S rS c bS 
                              (A_eqv_symmetric _ _ eqvS)
                              (A_sg_C_anti_right_d _ _ _ sgS) 
                              (A_sg_C_right_cancel_d _ _ _ sgS) 
; A_sg_C_left_constant_d  := inr _ (bop_add_id_not_left_constant S rS c bS 
                                    (A_eqv_nontrivial _ _ eqvS))
; A_sg_C_right_constant_d := inr _ (bop_add_id_not_right_constant S rS c bS 
                                    (A_eqv_nontrivial _ _ eqvS))
; A_sg_C_anti_left_d      := inr _ (bop_add_id_not_anti_left S rS c bS
                                   (A_eqv_reflexive _ _ eqvS)                                                             
                                    (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_C_anti_right_d     := inr _ (bop_add_id_not_anti_right S rS c bS
                                      (A_eqv_reflexive _ _ eqvS)
                                      (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
|}. 

Definition sg_CI_proofs_add_id : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
     eqv_proofs S rS -> 
     sg_CI_proofs S rS bS -> 
        sg_CI_proofs (with_constant S) (brel_add_constant rS c) (bop_add_id bS c)
:= λ S rS c bS eqvS sgS, 
{|
  A_sg_CI_associative        := bop_add_id_associative S rS c bS 
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_sg_CI_associative _ _ _ sgS)
; A_sg_CI_congruence         := bop_add_id_congruence S rS c bS 
                                  (A_eqv_symmetric _ _ eqvS)
                                  (A_sg_CI_congruence _ _ _ sgS) 
; A_sg_CI_commutative        := bop_add_id_commutative S rS c bS 
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_sg_CI_commutative _ _ _ sgS)
; A_sg_CI_idempotent         := bop_add_id_idempotent S rS c bS 
                                  (A_sg_CI_idempotent _ _ _ sgS)
; A_sg_CI_selective_d        := bop_add_id_selective_decide S rS c bS 
                                 (A_eqv_reflexive _ _ eqvS)
                                 (A_sg_CI_selective_d _ _ _ sgS)
; A_sg_CI_exists_id_d        := inl _ (bop_add_id_exists_id S rS c bS (A_eqv_reflexive _ _ eqvS))
; A_sg_CI_exists_ann_d       := bop_add_id_exists_ann_decide S rS c bS 
                                  (A_eqv_nontrivial _ _ eqvS)
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_sg_CI_exists_ann_d _ _ _ sgS) 
|}. 

Definition sg_CS_proofs_add_id : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
     eqv_proofs S rS -> 
     sg_CS_proofs S rS bS -> 
        sg_CS_proofs (with_constant S) (brel_add_constant rS c) (bop_add_id bS c)
:= λ S rS c bS eqvS sgS, 
{|
  A_sg_CS_associative   := bop_add_id_associative S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_CS_associative _ _ _ sgS)
; A_sg_CS_congruence    := bop_add_id_congruence S rS c bS 
                           (A_eqv_symmetric _ _ eqvS)
                           (A_sg_CS_congruence _ _ _ sgS) 
; A_sg_CS_commutative   := bop_add_id_commutative S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_CS_commutative _ _ _ sgS)
; A_sg_CS_selective     := bop_add_id_selective S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_CS_selective _ _ _ sgS)
; A_sg_CS_exists_id_d   := inl _ (bop_add_id_exists_id S rS c bS (A_eqv_reflexive _ _ eqvS))
; A_sg_CS_exists_ann_d  := bop_add_id_exists_ann_decide S rS c bS 
                           (A_eqv_nontrivial _ _ eqvS)
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_CS_exists_ann_d _ _ _ sgS) 
|}.




Definition A_sg_add_id : ∀ (S : Type) (c : cas_constant),  A_sg S -> A_sg (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_eq        := A_eqv_add_constant S (A_sg_eq S sgS) c  
   ; A_sg_bop       := bop_add_id (A_sg_bop S sgS) c 
   ; A_sg_proofs    := sg_proofs_add_id S (A_eqv_eq S (A_sg_eq S sgS)) c 
                                           (A_sg_bop S sgS) 
                                           (A_eqv_proofs S (A_sg_eq S sgS))
                                           (A_sg_proofs S sgS) 
   ; A_sg_ast       := Ast_sg_add_id (c, A_sg_ast S sgS)
   |}. 


Definition A_sg_C_add_id : ∀ (S : Type) (c : cas_constant),  A_sg_C S -> A_sg_C (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_C_eqv       := A_eqv_add_constant S (A_sg_C_eqv S sgS) c  
   ; A_sg_C_bop       := bop_add_id (A_sg_C_bop S sgS) c 
   ; A_sg_C_proofs    := sg_C_proofs_add_id S (A_eqv_eq S (A_sg_C_eqv S sgS)) c 
                                           (A_sg_C_bop S sgS) 
                                           (A_eqv_proofs S (A_sg_C_eqv S sgS))
                                           (A_sg_C_proofs S sgS) 
   ; A_sg_C_ast       := Ast_sg_C_add_id (c, A_sg_C_ast S sgS)
   |}. 


Definition A_sg_CI_add_id : ∀ (S : Type) (c : cas_constant), A_sg_CI S -> A_sg_CI (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_CI_eqv       := A_eqv_add_constant S (A_sg_CI_eqv S sgS) c  
   ; A_sg_CI_bop       := bop_add_id (A_sg_CI_bop S sgS) c 
   ; A_sg_CI_proofs    := sg_CI_proofs_add_id S (A_eqv_eq S (A_sg_CI_eqv S sgS)) c 
                                           (A_sg_CI_bop S sgS) 
                                           (A_eqv_proofs S (A_sg_CI_eqv S sgS))
                                           (A_sg_CI_proofs S sgS) 
   ; A_sg_CI_ast       := Ast_sg_CI_add_id (c, A_sg_CI_ast S sgS)
   |}. 


Definition A_sg_CS_add_id : ∀ (S : Type) (c : cas_constant),  A_sg_CS S -> A_sg_CS (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_CS_eqv       := A_eqv_add_constant S (A_sg_CS_eqv S sgS) c  
   ; A_sg_CS_bop       := bop_add_id (A_sg_CS_bop S sgS) c 
   ; A_sg_CS_proofs    := sg_CS_proofs_add_id S (A_eqv_eq S (A_sg_CS_eqv S sgS)) c 
                                           (A_sg_CS_bop S sgS) 
                                           (A_eqv_proofs S (A_sg_CS_eqv S sgS))
                                           (A_sg_CS_proofs S sgS) 
   ; A_sg_CS_ast       := Ast_sg_CS_add_id (c, A_sg_CS_ast S sgS)
   |}. 

