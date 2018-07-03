Require Import CAS.code.basic_types. 
Require Import CAS.code.bop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.facts.

Section Left.

  Variable S : Type.
  Variable r : brel S.
  Variable wS : S. 
  Variable f : S -> S.

  Variable Pf : brel_not_trivial S r f. 
  Variable refS : brel_reflexive S r. 

Lemma bop_left_associative : bop_associative S r (@bop_left S).
Proof. intros s t u.  unfold bop_left.  apply (refS s). Qed. 

Lemma bop_left_congruence : bop_congruence S r (@bop_left S).
Proof. intros s t u v H Q. unfold bop_left. exact H. Qed. 

Lemma bop_left_not_commutative : bop_not_commutative S r (@bop_left S).
Proof. exists (wS, f wS). destruct (Pf wS) as [L _]. unfold bop_left. exact L. Defined. 

Lemma bop_left_idempotent : bop_idempotent S r (@bop_left S).
Proof. intro s. unfold bop_left. apply (refS s). Qed. 

Lemma bop_left_selective : bop_selective S r (@bop_left S).
Proof. intros s t. unfold bop_left. left. apply (refS s).  Qed. 

Lemma bop_left_is_left : bop_is_left S r (@bop_left S).
Proof. intros s t. unfold bop_left. apply (refS s). Qed. 

Lemma bop_left_not_is_right : bop_not_is_right S r (@bop_left S).
Proof. exists (wS, f wS). destruct (Pf wS) as [L _]. unfold bop_left. exact L. Defined. 

Lemma bop_left_not_exists_id : bop_not_exists_id S r (@bop_left S).
Proof. intro i. exists (f i). destruct (Pf i) as [L _]. left. unfold bop_left. exact L. Defined. 

Lemma bop_left_not_exists_ann : bop_not_exists_ann S r (@bop_left S).
Proof. intro a.  exists (f a). destruct (Pf a) as [_ R]. right. unfold bop_left. exact R. Defined. 

Lemma bop_left_not_left_cancellative : bop_not_left_cancellative S r (@bop_left S). 
Proof. exists (wS, (wS, f wS)); compute. destruct (Pf wS) as [L R]. split. apply (refS wS). exact L. Defined. 

Lemma bop_left_right_cancellative : bop_right_cancellative S r (@bop_left S). 
Proof. intros s t u. compute. auto. Qed. 

Lemma bop_left_left_constant : bop_left_constant S r (@bop_left S). 
Proof. intros s t u. compute. auto. Qed. 

Lemma bop_left_not_right_constant : bop_not_right_constant S r (@bop_left S). 
Proof. exists (wS, (wS, f wS)); compute. destruct (Pf wS) as [L _]. exact L. Defined. 

Lemma bop_left_not_anti_left : bop_not_anti_left S r (@bop_left S). 
Proof. exists (wS, wS); compute. apply (refS wS). Defined.

Lemma bop_left_not_anti_right : bop_not_anti_right S r (@bop_left S). 
Proof. exists (wS, wS); compute. apply (refS wS). Defined.

End Left. 