Require Import CAS.code.basic_types. 
Require Import CAS.code.bop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.facts. 

Lemma bop_left_associative : 
   ∀ (S : Type) (r : brel S),  (brel_reflexive S r) -> bop_associative S r (bop_left S).
Proof. unfold bop_associative. intros S r refS s t u. 
       unfold bop_left.  unfold brel_reflexive in refS. apply refS. Defined. 

Lemma bop_left_congruence : 
   ∀ (S : Type) (r : brel S), bop_congruence S r (bop_left S).
Proof. unfold bop_congruence. intros S r s t u v H Q. unfold bop_left. assumption. Defined. 

Lemma bop_left_not_commutative : 
   ∀ (S : Type) (r : brel S), (brel_nontrivial S r) -> bop_not_commutative S r (bop_left S).
Proof. intros S r nt. 
       destruct (brel_nontrivial_witness S r nt) as [s sP]. 
       destruct (brel_nontrivial_negate S r nt) as [f fP]. 
       exists (s, f s). destruct (fP s) as [L R]. 
       unfold bop_left. assumption. 
Defined. 

Lemma bop_left_idempotent : 
   ∀ (S : Type) (r : brel S), (brel_reflexive S r) -> bop_idempotent S r (bop_left S).
Proof. intros S r ref s. unfold bop_left. apply ref. 
Defined. 

Lemma bop_left_selective : 
   ∀ (S : Type) (r : brel S), (brel_reflexive S r) -> bop_selective S r (bop_left S).
Proof. intros S r ref s t. unfold bop_left. left. apply ref. 
Defined. 

Lemma bop_left_is_left : 
   ∀ (S : Type) (r : brel S), (brel_reflexive S r) -> bop_is_left S r (bop_left S).
Proof. intros S r ref s t. unfold bop_left. apply ref. Defined. 

Lemma bop_left_not_is_right : 
   ∀ (S : Type) (r : brel S), (brel_nontrivial S r) -> bop_not_is_right S r (bop_left S).
Proof. intros S r nt. 
       destruct (brel_nontrivial_witness S r nt) as [s sP]. 
       destruct (brel_nontrivial_negate S r nt) as [f fP]. 
       exists (s, f s). destruct (fP s) as [L R]. 
       unfold bop_left, bop_not_is_right. 
       assumption. 
Defined. 

Lemma bop_left_not_exists_id : 
   ∀ (S : Type) (r : brel S), (brel_nontrivial S r) -> bop_not_exists_id S r (bop_left S).
Proof. intros S r nt. unfold bop_left, bop_not_exists_id. 
       intro i. destruct (brel_nontrivial_negate S r nt) as [f Pf].
       exists (f i). destruct (Pf i) as [L R]. left. assumption. 
Defined. 


Lemma bop_left_not_exists_ann : 
   ∀ (S : Type) (r : brel S), (brel_nontrivial S r) -> bop_not_exists_ann S r (bop_left S).
Proof. unfold bop_left, bop_not_exists_ann. 
       intros S r nt a.  
       destruct (brel_nontrivial_negate S r nt) as [f Pf].
       exists (f a). destruct (Pf a) as [L R]. right. assumption. 
Defined. 

Definition bop_left_not_exists_ann_v2 : 
     ∀ (S : Type) (r : brel S),
       brel_nontrivial S r → bop_not_exists_ann S r (bop_left S)
:= λ (S : Type) 
     (r : brel S) 
     (nt : brel_nontrivial S r) 
     (a : S), 
     let (f, Pf) := brel_nontrivial_negate S r nt in
       existT (λ s : S, (r a a = false) + (r s a = false)) 
              (f a) 
              (inr (snd (Pf a))).



Lemma bop_left_not_left_cancellative : ∀ (S : Type) (r : brel S),
         brel_reflexive S r -> 
         brel_nontrivial S r -> 
            bop_not_left_cancellative S r (bop_left S). 
Proof. intros S r refS [[s Ps] [f Pf]]. 
       exists (s, (s, f s)); compute. 
       destruct (Pf s) as [L R]. auto. 
Defined. 


Lemma bop_left_right_cancellative : ∀ (S : Type) (r : brel S),
            bop_right_cancellative S r (bop_left S). 
Proof. intros S r refS s t u. compute. auto. Qed. 


Lemma bop_left_left_constant : ∀ (S : Type) (r : brel S),
         brel_reflexive S r -> 
            bop_left_constant S r (bop_left S). 
Proof. intros S r refS s t u. compute. auto. Qed. 

Lemma bop_left_not_right_constant : ∀ (S : Type) (r : brel S),
         brel_nontrivial S r -> 
            bop_not_right_constant S r (bop_left S). 
Proof. intros S r [[s Ps] [f Pf]]. 
       exists (s, (s, f s)); compute.        
       destruct (Pf s) as [L R]. auto. 
Defined. 
       

Lemma bop_left_not_anti_left : ∀ (S : Type) (r : brel S),
         brel_witness S r ->  bop_not_anti_left S r (bop_left S). 
Proof. intros S r [s Ps]. exists (s, s); compute. assumption. Defined. 

Lemma bop_left_not_anti_right : ∀ (S : Type) (r : brel S),
         brel_witness S r ->  bop_not_anti_right S r (bop_left S). 
Proof. intros S r [s Ps]. exists (s, s); compute. assumption. Defined. 

