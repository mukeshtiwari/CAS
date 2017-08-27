Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.bop.left.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.

Definition sg_proofs_left : ∀ (S : Type) (rS : brel S), 
              (eqv_proofs S rS) → sg_proofs S rS (@bop_left S)
:= λ S rS eqvS, 
{| 
  A_sg_associative   := bop_left_associative S rS (A_eqv_reflexive _ _ eqvS)
; A_sg_congruence    := bop_left_congruence S rS 
; A_sg_commutative_d := inr _ (bop_left_not_commutative S rS (A_eqv_nontrivial _ _ eqvS))
; A_sg_selective_d   := inl _ (bop_left_selective S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_is_left_d     := inl _ (bop_left_is_left S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_is_right_d    := inr _ (bop_left_not_is_right S rS (A_eqv_nontrivial _ _ eqvS))
; A_sg_idempotent_d  := inl _ (bop_left_idempotent S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_exists_id_d   := inr _ (bop_left_not_exists_id S rS (A_eqv_nontrivial _ _ eqvS))
; A_sg_exists_ann_d  := inr _ (bop_left_not_exists_ann S rS (A_eqv_nontrivial _ _ eqvS))
; A_sg_left_cancel_d    := inr _ (bop_left_not_left_cancellative S rS
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_nontrivial _ _ eqvS))
; A_sg_right_cancel_d   := inl _ (bop_left_right_cancellative S rS) 
; A_sg_left_constant_d  := inl _ (bop_left_left_constant S rS
                                    (A_eqv_reflexive _ _ eqvS))
; A_sg_right_constant_d := inr _ (bop_left_not_right_constant S rS
                                    (A_eqv_nontrivial _ _ eqvS))
; A_sg_anti_left_d      := inr _ (bop_left_not_anti_left S rS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_anti_right_d     := inr _ (bop_left_not_anti_right S rS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
|}. 


Definition A_sg_left: ∀ (S : Type),  A_eqv S -> A_sg S 
:= λ S eqvS, 
   {| 
     A_sg_eq        := eqvS
   ; A_sg_bop       := @bop_left S 
   ; A_sg_proofs    := sg_proofs_left S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS) 
   ; A_sg_ast       := Ast_sg_left (A_eqv_ast _ eqvS)
   |}. 

