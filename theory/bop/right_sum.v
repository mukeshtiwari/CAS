Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.facts. 

Lemma bop_right_sum_congruence : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_reflexive S rS → bop_congruence S rS bS → bop_congruence T rT bT → 
      bop_congruence (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   unfold bop_congruence. intros S T rS rT bS bT refS.  intros L R.
   intros [s1 | t1] [s2 | t2] [s3 | t3] [s4 | t4]; simpl.
   apply L. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   intros. assumption. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   intros. assumption. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   apply R. 
Defined. 

Lemma bop_right_sum_associative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_reflexive T rT → bop_associative S rS bS → bop_associative T rT bT → 
      bop_associative (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT refT. unfold bop_associative. intros L R.
   intros [s1 | t1] [s2 | t2] [s3 | t3]; simpl.
   apply L. apply refT. apply refT. apply refT. apply refT. apply refT. apply refT. apply R. 
Defined. 



Lemma bop_right_sum_idempotent : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_idempotent S rS bS → 
      bop_idempotent T rT bT → 
      bop_idempotent (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_idempotent. intros L R d. 
   destruct d; simpl. apply L. apply R. 
Defined. 

Lemma bop_right_sum_not_idempotent_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_not_idempotent S rS bS → 
      bop_not_idempotent (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_not_idempotent. intros [s P]. 
   exists (inl _ s). simpl. assumption. 
Defined. 

Lemma bop_right_sum_not_idempotent_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_not_idempotent T rT bT → 
      bop_not_idempotent (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_not_idempotent. intros [t P]. 
   exists (inr _ t). simpl. assumption. 
Defined. 

Lemma bop_right_sum_not_idempotent : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      (bop_not_idempotent S rS bS) + (bop_not_idempotent T rT bT) → 
      bop_not_idempotent (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT d. destruct d. 
   apply bop_right_sum_not_idempotent_left. assumption. 
   apply bop_right_sum_not_idempotent_right. assumption. 
Defined. 



Lemma bop_right_sum_commutative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_reflexive T rT → 
      bop_commutative S rS bS → 
      bop_commutative T rT bT → 
      bop_commutative (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT refl_rT. unfold bop_commutative. intros L R d1 d2. 
   destruct d1; destruct d2; simpl. 
      apply L. 
      apply refl_rT.
      apply refl_rT.
      apply R. 
Defined. 

Lemma bop_right_sum_not_commutative_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_not_commutative S rS bS → 
      bop_not_commutative (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_not_commutative. intros [ [s t] P]. 
   exists (inl _ s, inl _ t). simpl. assumption. 
Defined. 

Lemma bop_right_sum_not_commutative_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_not_commutative T rT bT → 
      bop_not_commutative (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_not_commutative. intros [ [s t] P]. 
   exists (inr _ s, inr _ t). simpl. assumption. 
Defined. 

Lemma bop_right_sum_not_commutative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      (bop_not_commutative S rS bS) + (bop_not_commutative T rT bT) → 
      bop_not_commutative (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT d. destruct d. 
   apply bop_right_sum_not_commutative_left. assumption. 
   apply bop_right_sum_not_commutative_right. assumption. 
Defined. 



Lemma bop_right_sum_selective : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_reflexive T rT → 
      bop_selective S rS bS → 
      bop_selective T rT bT → 
      bop_selective (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT refl_rT. unfold bop_selective. intros L R.
   intros [s1 | t1] [s2 | t2]; simpl.
      apply L. 
      right. apply refl_rT. 
      left. apply refl_rT. 
      apply R. 
Defined. 

Lemma bop_right_sum_not_selective_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_not_selective S rS bS → 
      bop_not_selective (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_not_selective. intros [ [s1 s2] P].
   exists (inl _ s1, inl _ s2). simpl. assumption. 
Defined. 


Lemma bop_right_sum_not_selective_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_not_selective T rT bT → 
      bop_not_selective (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_not_selective. intros [ [t1 t2] P].
   exists (inr _ t1, inr _ t2). simpl. assumption. 
Defined. 

Lemma bop_right_sum_not_selective : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      (bop_not_selective S rS bS) + (bop_not_selective T rT bT) → 
      bop_not_selective (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT [L | R]. 
   apply bop_right_sum_not_selective_left. assumption. 
   apply bop_right_sum_not_selective_right. assumption. 
Defined. 




Lemma bop_right_sum_not_is_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_witness S rS ->   brel_witness T rT ->  
      bop_not_is_left (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT [s _] [t _]. unfold bop_not_is_left. 
   exists (inl _ s, inr _ t). simpl. reflexivity. 
Defined. 

Lemma bop_right_sum_not_is_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_witness S rS ->   brel_witness T rT ->  
      bop_not_is_right (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT [s _] [t _]. unfold bop_not_is_right. 
   exists (inr _ t, inl _ s). simpl. reflexivity. 
Defined. 



Lemma bop_right_sum_exists_id : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T), 
       brel_reflexive T rT ->  
       ∀ (bS : binary_op S) (bT : binary_op T), 
         (bop_exists_id S rS bS) -> 
           bop_exists_id (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT).
Proof. unfold bop_exists_id. 
       intros S T rS rT refS bS bT [iS pS]. 
       exists (inl _ iS). 
          intros [s | t]. 
             compute. apply (pS s). 
             compute. rewrite (refS t); auto. 
Defined. 



Lemma bop_right_sum_not_exists_id : 
     ∀ (S T : Type) 
       (wS : S) 
       (rS : brel S) 
       (rT : brel T) 
       (bS : binary_op S) 
       (bT : binary_op T), 
         (bop_not_exists_id S rS bS) -> 
           bop_not_exists_id (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT).
Proof. unfold bop_not_exists_id. intros S T wS rS rT bS bT pS [s | t].
       destruct (pS s) as [x D]. exists (inl _ x). compute. assumption. 
       exists (inl _ wS). compute. auto. 
Defined. 



Lemma bop_right_sum_exists_ann : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T), 
       brel_reflexive T rT ->  
       ∀ (bS : binary_op S) (bT : binary_op T), 
         (bop_exists_ann T rT bT) -> 
           bop_exists_ann (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT).
Proof. unfold bop_exists_ann. 
       intros S T rS rT refT bS bT [annT pT]. 
       exists (inr _ annT). 
          intros [s | t]. 
             compute. rewrite (refT annT); auto. 
             compute. apply (pT t). 
Defined. 

Lemma bop_right_sum_not_exists_ann : 
     ∀ (S T : Type) (witness : T) (rS : brel S) (rT : brel T), 
       brel_reflexive T rT ->  
       ∀ (bS : binary_op S) (bT : binary_op T), 
         (bop_not_exists_ann T rT bT) -> 
           bop_not_exists_ann (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT).
Proof. unfold bop_not_exists_ann. 
       intros S T witness rS rT refS bS bT pT [s | t]. 
       exists (inr _ witness). compute; auto.  
       destruct (pT t) as [x D].  exists (inr _ x). compute. assumption. 
Defined. 




Lemma bop_right_sum_not_left_cancellative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_witness T rT -> 
      brel_nontrivial S rS -> 
      bop_not_left_cancellative (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT). 
Proof. intros S T rS rT bS bT [t Pt] [[s Ps] [f Pf]]. 
       destruct (Pf s) as [L R]. 
       exists ((inr _ t), ((inl s), (inl (f s)))). simpl. auto. 
Defined. 

Lemma bop_right_sum_not_right_cancellative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_witness T rT -> 
      brel_nontrivial S rS -> 
      bop_not_right_cancellative (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT). 
Proof. intros S T rS rT bS bT [t Pt] [[s Ps] [f Pf]]. 
       destruct (Pf s) as [L R]. 
       exists ((inr _ t), ((inl s), (inl (f s)))). simpl.  auto. 
Defined. 


Lemma bop_right_sum_not_left_constant : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_witness S rS -> 
      brel_nontrivial T rT -> 
      bop_not_left_constant (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT). 
Proof. intros S T rS rT bS bT [s Ps] [[t Pt] [f Pf]]. 
       destruct (Pf t) as [L R]. 
       exists (inl s, (inr t, inr (f t))). simpl.  auto. 
Defined. 


Lemma bop_right_sum_not_right_constant : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_witness S rS -> 
      brel_nontrivial T rT -> 
      bop_not_right_constant (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT). 
Proof. intros S T rS rT bS bT [s Ps] [[t Pt] [f Pf]]. 
       destruct (Pf t) as [L R]. 
       exists (inl s, (inr t, inr (f t))). simpl.  auto. 
Defined. 




Lemma bop_right_sum_not_anti_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T),
      brel_witness S rS -> 
      brel_witness T rT -> 
      bop_not_anti_left (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT). 
Proof. intros S T rS rT bS bT [s Ps] [t Pt]. 
       exists (inr t, inl s); simpl. assumption. 
Defined. 


Lemma bop_right_sum_not_anti_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T),
      brel_witness S rS -> 
      brel_witness T rT -> 
      bop_not_anti_right (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT). 
Proof. intros S T rS rT bS bT [s Ps] [t Pt]. 
       exists (inr t, inl s); simpl. assumption. 
Defined. 




