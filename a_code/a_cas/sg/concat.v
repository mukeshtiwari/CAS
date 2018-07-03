Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.brel.eq_list. 
Require Import CAS.theory.bop.concat.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cas.eqv.list. 
Require Import CAS.theory.facts. 


(* NB : this is cancellative, but not commutative .... 
   want versions of lex to work for this ...
*) 
Definition sg_proofs_concat : 
   ∀ (S : Type) (rS : brel S) (s : S) (f : S -> S), 
     brel_not_trivial S rS f -> eqv_proofs S rS -> sg_proofs (list S) (brel_list rS) (@bop_concat S)
:= λ S rS s f Pf eqvS, 
{|
  A_sg_associative   := bop_concat_associative S rS (A_eqv_reflexive _ _ eqvS)
; A_sg_congruence    := bop_concat_congruence S rS (A_eqv_reflexive _ _ eqvS)
; A_sg_commutative_d := inr _ (bop_concat_not_commutative S rS s f Pf)
; A_sg_selective_d   := inr _ (bop_concat_not_selective S rS s f Pf)
; A_sg_is_left_d     := inr _ (bop_concat_not_is_left S rS s)
; A_sg_is_right_d    := inr _ (bop_concat_not_is_right S rS s)
; A_sg_idempotent_d  := inr _ (bop_concat_not_idempotent S rS s)
; A_sg_exists_id_d   := inl _ (bop_concat_exists_id S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_exists_ann_d  := inr _ (bop_concat_not_exists_ann S rS s )
; A_sg_left_cancel_d    := inl _ (bop_concat_left_cancellative S rS (A_eqv_reflexive S rS eqvS))
; A_sg_right_cancel_d   := inl _ (bop_concat_right_cancellative S rS)
; A_sg_left_constant_d  := inr _ (bop_concat_not_left_constant S rS s)
; A_sg_right_constant_d := inr _ (bop_concat_not_right_constant S rS s)
; A_sg_anti_left_d      := inr _ (bop_concat_not_anti_left S rS s (A_eqv_reflexive _ _ eqvS))
; A_sg_anti_right_d     := inr _ (bop_concat_not_anti_right S rS s (A_eqv_reflexive _ _ eqvS))
|}. 
 
Definition A_sg_concat : ∀ (S : Type),  A_eqv S -> A_sg (list S) 
:= λ S eqvS, 
   {| 
     A_sg_eq         := A_eqv_list S eqvS
   ; A_sg_bop        := @bop_concat S 
   ; A_sg_proofs     := sg_proofs_concat S (A_eqv_eq S eqvS)
                                         (A_eqv_witness S eqvS)
                                         (A_eqv_new S eqvS)
                                         (A_eqv_not_trivial S eqvS)
                                         (A_eqv_proofs S eqvS) 
   ; A_sg_ast        := Ast_sg_concat (A_eqv_ast S eqvS)
   |}. 

