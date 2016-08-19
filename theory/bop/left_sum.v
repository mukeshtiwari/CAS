Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 

Lemma bop_left_sum_congruence : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_reflexive S rS → bop_congruence S rS bS → bop_congruence T rT bT → 
      bop_congruence (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
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


Lemma bop_left_sum_associative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_reflexive S rS → bop_associative S rS bS → bop_associative T rT bT → 
      bop_associative (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT refS. unfold bop_associative. intros L R.
   intros [s1 | t1] [s2 | t2] [s3 | t3]; simpl.
   apply L. apply refS. apply refS. apply refS. apply refS. apply refS. apply refS. apply R. 
Defined. 


Lemma bop_left_sum_idempotent : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_idempotent S rS bS → 
      bop_idempotent T rT bT → 
      bop_idempotent (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_idempotent. intros L R d. 
   destruct d; simpl. apply L. apply R. 
Defined. 

(* Note: no need for "brel_reflexive S rS" here *) 
Lemma bop_left_sum_not_idempotent_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_not_idempotent S rS bS → 
      bop_not_idempotent (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_not_idempotent. intros [s P]. 
   exists (inl _ s). simpl. assumption. 
Defined. 

Lemma bop_left_sum_not_idempotent_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_not_idempotent T rT bT → 
      bop_not_idempotent (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_not_idempotent. intros [t P]. 
   exists (inr _ t). simpl. assumption. 
Defined. 

Lemma bop_left_sum_idempotent_comp : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      (bop_not_idempotent S rS bS) + (bop_not_idempotent T rT bT) → 
      bop_not_idempotent (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT d. destruct d. 
   apply bop_left_sum_not_idempotent_left. assumption. 
   apply bop_left_sum_not_idempotent_right. assumption. 
Defined. 



Lemma bop_left_sum_commutative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_reflexive S rS → 
      bop_commutative S rS bS → 
      bop_commutative T rT bT → 
      bop_commutative (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT refl_rS. unfold bop_commutative. intros L R d1 d2. 
   destruct d1; destruct d2; simpl. 
      apply L. 
      apply refl_rS.
      apply refl_rS.
      apply R. 
Defined. 

Lemma bop_left_sum_not_commutative_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_not_commutative S rS bS → 
      bop_not_commutative (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_not_commutative. intros [ [s t] P]. 
   exists (inl _ s, inl _ t). simpl. assumption. 
Defined. 

Lemma bop_left_sum_not_commutative_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_not_commutative T rT bT → 
      bop_not_commutative (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_not_commutative. intros [ [s t] P]. 
   exists (inr _ s, inr _ t). simpl. assumption. 
Defined. 

Lemma bop_left_sum_not_commutative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      (bop_not_commutative S rS bS) + (bop_not_commutative T rT bT) → 
      bop_not_commutative (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT d. destruct d. 
   apply bop_left_sum_not_commutative_left. assumption. 
   apply bop_left_sum_not_commutative_right. assumption. 
Defined. 

Lemma bop_left_sum_selective : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_reflexive S rS → 
      bop_selective S rS bS → 
      bop_selective T rT bT → 
      bop_selective (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT refl_rS. unfold bop_selective. intros L R.
   intros [s1 | t1] [s2 | t2]; simpl.
      apply L. 
      left. apply refl_rS. 
      right. apply refl_rS. 
      apply R. 
Defined. 

Lemma bop_left_sum_not_selective_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_not_selective S rS bS → 
      bop_not_selective (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_not_selective. intros [ [s1 s2] P].
   exists (inl _ s1, inl _ s2). simpl. assumption. 
Defined. 

Lemma bop_left_sum_not_selective_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_not_selective T rT bT → 
      bop_not_selective (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_not_selective. intros [ [t1 t2] P].
   exists (inr _ t1, inr _ t2). simpl. assumption. 
Defined. 

Lemma bop_left_sum_not_selective : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      (bop_not_selective S rS bS) + (bop_not_selective T rT bT) → 
      bop_not_selective (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT [L | R]. 
   apply bop_left_sum_not_selective_left. assumption. 
   apply bop_left_sum_not_selective_right. assumption. 
Defined. 


Lemma bop_left_sum_not_is_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T),
      brel_witness S rS ->   brel_witness T rT ->  
      bop_not_is_left (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT [s _] [t _]. unfold bop_not_is_left. 
   exists (inr _ t, inl _ s). simpl. reflexivity. 
Defined. 

Lemma bop_left_sum_not_is_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_witness S rS ->   brel_witness T rT ->  
      bop_not_is_right (S + T) (brel_sum _ _ rS rT) (bop_left_sum _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT [s _] [t _]. unfold bop_not_is_right. 
   exists (inl _ s, inr _ t). simpl. reflexivity. 
Defined. 

Lemma bop_left_sum_exists_id : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T), 
       brel_reflexive S rS ->  
       ∀ (bS : binary_op S) (bT : binary_op T), 
         (bop_exists_id T rT bT) -> 
           bop_exists_id (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT).
Proof. unfold bop_exists_id. 
       intros S T rS rT refS bS bT [iT pT]. 
       exists (inr _ iT). 
          intros [s | t]. 
             compute. rewrite (refS s); auto. 
             compute. apply (pT t). 
Defined. 


Lemma bop_left_sum_not_exists_id : 
     ∀ (S T : Type) 
       (wT : T) 
       (rS : brel S) 
       (rT : brel T) 
       (bS : binary_op S) 
       (bT : binary_op T), 
         (bop_not_exists_id T rT bT) -> 
           bop_not_exists_id (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT).
Proof. unfold bop_not_exists_id. intros S T wT rS rT bS bT pT [s | t].
       exists (inr _ wT). compute. auto. 
       destruct (pT t) as [x D]. exists (inr _ x). compute. assumption. 
Defined. 


Lemma bop_left_sum_exists_ann : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T), 
       brel_reflexive S rS ->  
       ∀ (bS : binary_op S) (bT : binary_op T), 
         (bop_exists_ann S rS bS) -> 
           bop_exists_ann (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT).
Proof. unfold bop_exists_ann. 
       intros S T rS rT refS bS bT [annS pS]. 
       exists (inl _ annS). 
          intros [s | t]. 
             compute. apply (pS s). 
             compute. rewrite (refS annS); auto. 
Defined. 


Lemma bop_left_sum_not_exists_ann : 
     ∀ (S T : Type) (witness : S) (rS : brel S) (rT : brel T), 
       brel_reflexive S rS ->  
       ∀ (bS : binary_op S) (bT : binary_op T), 
         (bop_not_exists_ann S rS bS) -> 
           bop_not_exists_ann (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT).
Proof. unfold bop_not_exists_ann. 
       intros S T witness rS rT refS bS bT pS [s | t]. 
       destruct (pS s) as [x D].  exists (inl _ x). compute. assumption. 
       exists (inl _ witness). compute; auto.  
Defined. 



Lemma bop_left_sum_not_left_cancellative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_witness S rS -> 
      brel_nontrivial T rT -> 
      bop_not_left_cancellative (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT). 
Proof. intros S T rS rT bS bT [s Ps] [[t Pt] [f Pf]]. 
       destruct (Pf t) as [L R]. 
       exists ((inl _ s), ((inr t), (inr (f t)))). simpl.  auto. 
Defined. 

Lemma bop_left_sum_not_right_cancellative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_witness S rS -> 
      brel_nontrivial T rT -> 
      bop_not_right_cancellative (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT). 
Proof. intros S T rS rT bS bT [s Ps] [[t Pt] [f Pf]]. 
       destruct (Pf t) as [L R]. 
       exists ((inl _ s), ((inr t), (inr (f t)))). simpl.  auto. 
Defined. 


Lemma bop_left_sum_not_left_constant : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_witness T rT -> 
      brel_nontrivial S rS -> 
      bop_not_left_constant (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT). 
Proof. intros S T rS rT bS bT [t Pt] [[s Ps] [f Pf]]. 
       destruct (Pf s) as [L R]. 
       exists (inr t, (inl s, inl (f s))). simpl.  auto. 
Defined. 


Lemma bop_left_sum_not_right_constant : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_witness T rT -> 
      brel_nontrivial S rS -> 
      bop_not_right_constant (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT). 
Proof. intros S T rS rT bS bT [t Pt] [[s Ps] [f Pf]]. 
       destruct (Pf s) as [L R]. 
       exists (inr t, (inl s, inl (f s))). simpl.  auto. 
Defined. 




Lemma bop_left_sum_not_anti_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T),
      brel_witness S rS -> 
      brel_witness T rT -> 
      bop_not_anti_left (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT). 
Proof. intros S T rS rT bS bT [s Ps] [t Pt]. 
       exists (inl s, inr t); simpl. assumption. 
Defined. 


Lemma bop_left_sum_not_anti_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T),
      brel_witness S rS -> 
      brel_witness T rT -> 
      bop_not_anti_right (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT). 
Proof. intros S T rS rT bS bT [s Ps] [t Pt]. 
       exists (inl s, inr t); simpl. assumption. 
Defined. 





