Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.bop.right.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.

Definition sg_proofs_right : ∀ (S : Type) (rS : brel S) (s : S) (f : S -> S),
      brel_not_trivial S rS f → eqv_proofs S rS → sg_proofs S rS (@bop_right S)
:= λ S rS s f Pf eqvS, 
{| 
  A_sg_associative   := bop_right_associative S rS (A_eqv_reflexive _ _ eqvS)
; A_sg_congruence    := bop_right_congruence S rS 
; A_sg_commutative_d := inr _ (bop_right_not_commutative S rS s f Pf) 
; A_sg_selective_d   := inl _ (bop_right_selective S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_is_left_d     := inr _ (bop_right_not_is_left S rS s f Pf) 
; A_sg_is_right_d    := inl _ (bop_right_is_right S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_idempotent_d  := inl _ (bop_right_idempotent S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_exists_id_d   := inr _ (bop_right_not_exists_id S rS f Pf)
; A_sg_exists_ann_d  := inr _ (bop_right_not_exists_ann S rS f Pf) 
; A_sg_left_cancel_d    := inl _ (bop_right_left_cancellative S rS) 
; A_sg_right_cancel_d   := inr _ (bop_right_not_right_cancellative S rS s f Pf (A_eqv_reflexive _ _ eqvS))
; A_sg_left_constant_d  := inr _ (bop_right_not_left_constant S rS s f Pf)
; A_sg_right_constant_d := inl _ (bop_right_right_constant S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_anti_left_d      := inr _ (bop_right_not_anti_left S rS s (A_eqv_reflexive _ _ eqvS))
; A_sg_anti_right_d     := inr _ (bop_right_not_anti_right S rS s (A_eqv_reflexive _ _ eqvS))
|}. 



Definition A_sg_right : ∀ (S : Type),  A_eqv S -> A_sg S 
:= λ S eqvS, 
   {| 
     A_sg_eq         := eqvS
   ; A_sg_bop        := @bop_right S 
   ; A_sg_proofs     := sg_proofs_right S (A_eqv_eq S eqvS)
                                        (A_eqv_witness S eqvS)
                                        (A_eqv_new S eqvS)
                                        (A_eqv_not_trivial S eqvS)
                                        (A_eqv_proofs S eqvS) 
   ; A_sg_ast        := Ast_sg_right (A_eqv_ast _ eqvS)
   |}. 

