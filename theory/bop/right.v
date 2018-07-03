Require Import CAS.code.basic_types. 
Require Import CAS.code.bop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.facts. 

Section Right. 

  Variable S : Type.
  Variable r : brel S.
  Variable wS : S. 
  Variable f : S -> S.

  Variable Pf : brel_not_trivial S r f. 
  Variable refS : brel_reflexive S r. 

Lemma bop_right_associative : bop_associative S r (@bop_right S).
Proof. intros s t u. unfold bop_right. apply (refS u). Qed. 

Lemma bop_right_congruence : 
   ∀ (S : Type) (r : brel S), bop_congruence S r (@bop_right S).
Proof. intros s t u v H Q. compute. auto. Qed. 

Lemma bop_right_idempotent : bop_idempotent S r (@bop_right S).
Proof. intros s. unfold bop_right. apply (refS s). Qed. 

Lemma bop_right_not_commutative : bop_not_commutative S r (@bop_right S).
Proof. exists (f wS, wS). destruct (Pf wS) as [L R]. compute. exact L. Defined. 

Lemma bop_right_selective : bop_selective S r (@bop_right S).
Proof. intros s t. unfold bop_right. right. apply (refS t). Qed. 

Lemma bop_right_not_is_left : bop_not_is_left S r (@bop_right S).
Proof. exists (f wS, wS). compute. destruct (Pf wS) as [L _]. exact L. Defined. 

Lemma bop_right_is_right : bop_is_right S r (@bop_right S).
Proof. intros s t. unfold bop_right. apply (refS t). Qed. 

Lemma bop_right_not_exists_id : bop_not_exists_id S r (@bop_right S).
Proof. intro i.  exists (f i). compute. destruct (Pf i) as [L _]. right. exact L. Defined. 

Lemma bop_right_not_exists_ann : bop_not_exists_ann S r (@bop_right S).
Proof. intros a.  exists (f a). compute. destruct (Pf a) as [_ R]. left. exact R. Defined. 

Lemma bop_right_left_cancellative : bop_left_cancellative S r (@bop_right S). 
Proof. intros s t u. compute. auto. Qed. 

Lemma bop_right_not_right_cancellative : bop_not_right_cancellative S r (@bop_right S). 
Proof. exists (wS, (wS, f wS)); compute. destruct (Pf wS) as [L _]. split. apply (refS wS). exact L. Defined. 

Lemma bop_right_not_left_constant : bop_not_left_constant S r (@bop_right S). 
Proof. exists (wS, (wS, f wS)); compute. destruct (Pf wS) as [L _]. exact L. Defined. 

Lemma bop_right_right_constant : bop_right_constant S r (@bop_right S). 
Proof. intros s t u. compute. auto. Qed. 
       
Lemma bop_right_not_anti_left : bop_not_anti_left S r (@bop_right S). 
Proof. exists (wS, wS); compute. apply (refS wS). Defined. 

Lemma bop_right_not_anti_right : bop_not_anti_right S r (@bop_right S). 
Proof. exists (wS, wS); compute. apply (refS wS). Defined. 

End Right. 