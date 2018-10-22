Require Import CAS.coq.common.base.
Require Import CAS.coq.eqv.list.
Require Import CAS.coq.theory.facts. 



Definition ltr_cayley {S : Type} (b : binary_op S) : left_transform S S := b.


Section Theory.

  Variable S : Type.
  Variable eqS : brel S.
  Variable bS : binary_op S.
  Variable bS_cong : bop_congruence S eqS bS.
  Variable refS : brel_reflexive S eqS. 

  Print bop_congruence. 

 Lemma ltr_cayley_congruence : ltr_congruence S S eqS eqS (ltr_cayley bS).
 Proof. unfold ltr_congruence. unfold ltr_cayley. intros. apply bS_cong; auto. Qed.

 Lemma ltr_cayley_partial_congruence : ltr_partial_congruence S S eqS (ltr_cayley bS). 
 Proof. unfold ltr_congruence. intros s s1 s2 H.
        unfold ltr_cayley. apply bS_cong; auto. 
 Qed.

 Lemma ltr_cayley_is_right : bop_is_right S eqS bS -> ltr_is_right S S eqS (ltr_cayley bS).
 Proof. auto. Qed. 
 
 Lemma ltr_cayley_not_is_right : bop_not_is_right S eqS bS -> ltr_not_is_right S S eqS (ltr_cayley bS).
 Proof. auto. Qed. 
 
 Lemma ltr_cayley_cancellative : bop_left_cancellative S eqS bS -> ltr_left_cancellative S S eqS (ltr_cayley bS).
 Proof. auto. Qed.

 Lemma ltr_cayley_not_cancellative : bop_not_left_cancellative S eqS bS -> ltr_not_left_cancellative S S eqS (ltr_cayley bS).
 Proof. auto. Qed.
 
 Lemma ltr_cayley_exists_id : bop_exists_left_id S eqS bS -> ltr_exists_id S S eqS (ltr_cayley bS).
 Proof. auto. Qed. 

 Lemma ltr_cayley_not_exists_id : bop_not_exists_left_id S eqS bS -> ltr_not_exists_id S S eqS (ltr_cayley bS).
 Proof. auto. Qed. 
 
End Theory.

Section ACAS.

(*

Definition ltr_cayley_proofs (S : Type) (eqS : brel S) (bS : binary_op S) (sgP : sg_proofs S eqS bS) : ltr_proofs S S eqS eqS (ltr_cayley bS) := 
{|
  A_ltr_congruence          := ltr_cayley_congruence S eqS bS (A_sg_congruence _ _ _ sgP)
; A_ltr_is_right_d          := match A_sg_is_right_d _ _ _ sgP with
                                   | inl IR -> inl (ltr_cayley_is_right _ _ _ IR)
                                   | lnr NIR -> inr (ltr_cayley_not_is_right _ _ _ NIR)
                                   end 
; A_ltr_exists_id_d         := ????? 
; A_ltr_left_cancellative_d := match A_sg_is_left_cancellative_d _ _ _ sgP with
                                   | inl LC -> inl (ltr_cayley_is_cancellative _ _ _ LC)
                                   | lnr NLC -> inr (ltr_cayley_not_cancellative _ _ _ NLC)
                                   end 
|}.

Definition A_ltr_cons (S : Type) (A_sg S) :=
{|
  A_ltr_carrier := 
; A_ltr_label   := 
; A_ltr_trans   := 
; A_ltr_proofs  := 
; A_ltr_ast     := 
|}.
*) 

End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.   
  