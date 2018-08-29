Require Import CAS.coq.common.base.
Require Import CAS.coq.eqv.list.
Require Import CAS.coq.theory.facts. 

Section Theory.

 Open Scope list. 

 Definition ltr_cons : ∀ {S : Type}, left_transform S (list S) := λ {S} x y,  (x :: y) . 

 Lemma ltr_cons_congruence (S : Type) (eqS : brel S) : lt_congruence S (list S) eqS (brel_list eqS) ltr_cons. 
 Proof. unfold lt_congruence. intros s1 s2 l1 l2 H1 H2.
        unfold ltr_cons. unfold brel_list. fold (@brel_list S). rewrite H1, H2. compute; auto.
 Qed.
 
 Lemma ltr_cons_not_is_right (S : Type) (eqS : brel S) (s : S) : lt_not_is_right S (list S) (brel_list eqS) ltr_cons. 
 Proof. unfold lt_not_is_right. exists (s, nil). compute; auto. Defined.
 
 Lemma ltr_cons_not_exists_id (S : Type) (eqS : brel S) : lt_not_exists_id S (list S) (brel_list eqS) ltr_cons. 
 Proof. unfold lt_not_exists_id. intro s. unfold lt_not_is_id. exists nil. compute; auto. Defined.
 
 Lemma ltr_cons_cancellative (S : Type) (eqS : brel S) : lt_left_cancellative S (list S) (brel_list eqS) ltr_cons. 
 Proof. unfold lt_left_cancellative. intros s l1 l2 H. unfold ltr_cons in H. 
        unfold brel_list in H. fold (@brel_list S) in H. apply andb_is_true_left in H.
        destruct H as [_ H]. exact H.
Qed.        
 
End Theory.

Section ACAS.


Definition ltr_cons_proofs (S : Type) (eqS : brel S) (s : S) : ltr_proofs (list S) S (brel_list eqS) eqS (@ltr_cons S) := 
{|
  A_ltr_congruence          := ltr_cons_congruence S eqS
; A_ltr_is_right_d          := inr(ltr_cons_not_is_right S eqS s)
; A_ltr_exists_id_d         := inr(ltr_cons_not_exists_id S eqS)
; A_ltr_left_cancellative_d := inl(ltr_cons_cancellative S eqS)
|}.

Definition A_ltr_cons (S : Type) (eqv : A_eqv S) :=
{|
  A_ltr_carrier := A_eqv_list S eqv 
; A_ltr_label   := eqv                                                     
; A_ltr_trans   := @ltr_cons S 
; A_ltr_proofs  := ltr_cons_proofs S (A_eqv_eq S eqv) (A_eqv_witness S eqv)
; A_ltr_ast     := Ast_ltr_cons (A_eqv_ast S eqv) 
|}.

End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.   
  