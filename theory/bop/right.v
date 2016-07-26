
Require Import CAS.code.basic_types. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 

Lemma bop_right_associative : 
   ∀ (S : Type) (r : brel S),  (brel_reflexive S r) -> bop_associative S r (bop_right S).
Proof. unfold bop_associative. intros S r refS s t u. unfold bop_right. apply refS. Defined. 

Lemma bop_right_congruence : 
   ∀ (S : Type) (r : brel S), bop_congruence S r (bop_right S).
Proof. unfold bop_congruence. intros S r s t u v H Q. unfold bop_right. assumption. Defined. 


Lemma bop_right_idempotent : 
   ∀ (S : Type) (r : brel S), (brel_reflexive S r) -> bop_idempotent S r (bop_right S).
Proof. intros S r ref s. unfold bop_right. apply ref. Defined. 

Lemma bop_right_not_commutative : 
   ∀ (S : Type) (r : brel S), (brel_nontrivial S r) -> bop_not_commutative S r (bop_right S).
Proof. intros S r nt. 
       destruct (brel_nontrivial_witness S r nt) as [s sP]. 
       destruct (brel_nontrivial_negate S r nt) as [f fP]. 
       exists (f s, s). destruct (fP s) as [L R]. 
       unfold bop_left. assumption. 
Defined. 

Lemma bop_right_selective : 
   ∀ (S : Type) (r : brel S), (brel_reflexive S r) -> bop_selective S r (bop_right S).
Proof. intros S r ref s t. unfold bop_right. right. apply ref. Defined. 

Lemma bop_right_not_is_left : 
   ∀ (S : Type) (r : brel S), (brel_nontrivial S r) -> bop_not_is_left S r (bop_right S).
Proof. intros S r nt. 
       destruct (brel_nontrivial_witness S r nt) as [s sP]. 
       destruct (brel_nontrivial_negate S r nt) as [f fP]. 
       exists (f s, s). destruct (fP s) as [L R]. 
       unfold bop_left. assumption. 
Defined. 

Lemma bop_right_is_right : 
   ∀ (S : Type) (r : brel S), (brel_reflexive S r) -> bop_is_right S r (bop_right S).
Proof. intros S r ref s t. unfold bop_right. apply ref. Defined. 



Lemma bop_right_not_exists_id : 
   ∀ (S : Type) (r : brel S), (brel_nontrivial S r) -> bop_not_exists_id S r (bop_right S).
Proof. intros S r nt. unfold bop_right, bop_not_exists_id. 
       intro i. destruct (brel_nontrivial_negate S r nt) as [f Pf].
       exists (f i). destruct (Pf i) as [L R]. right. assumption. 
Defined. 

Lemma bop_right_not_exists_ann : 
   ∀ (S : Type) (r : brel S), (brel_nontrivial S r) -> bop_not_exists_ann S r (bop_right S).
Proof. unfold bop_right, bop_not_exists_ann. 
       intros S r nt a.  
       destruct (brel_nontrivial_negate S r nt) as [f Pf].
       exists (f a). destruct (Pf a) as [L R]. left. assumption. 
Defined. 



Lemma bop_right_left_cancellative : ∀ (S : Type) (r : brel S),
            bop_left_cancellative S r (bop_right S). 
Proof. intros S r s t u. compute. auto. Qed. 

Lemma bop_right_not_right_cancellative : ∀ (S : Type) (r : brel S),
         brel_reflexive S r -> 
         brel_nontrivial S r -> 
            bop_not_right_cancellative S r (bop_right S). 
Proof. intros S r refS [[s Ps] [f Pf]]. 
       exists (s, (s, f s)); compute. 
       destruct (Pf s) as [L R]. auto. 
Defined. 


Lemma bop_right_not_left_constant : ∀ (S : Type) (r : brel S),
         brel_nontrivial S r -> 
            bop_not_left_constant S r (bop_right S). 
Proof. intros S r [[s Ps] [f Pf]].        
       exists (s, (s, f s)); compute.
       destruct (Pf s) as [L R]. auto. 
Defined. 

Lemma bop_right_right_constant : ∀ (S : Type) (r : brel S),
         brel_reflexive S r -> 
            bop_right_constant S r (bop_right S). 
Proof. intros S r refS s t u. compute. auto. Qed. 

       
Lemma bop_right_not_anti_left : ∀ (S : Type) (r : brel S),
         brel_witness S r ->  bop_not_anti_left S r (bop_right S). 
Proof. intros S r [s Ps]. 
       exists (s, s); compute. assumption. 
Defined. 


Lemma bop_right_not_anti_right : ∀ (S : Type) (r : brel S),
         brel_witness S r ->  bop_not_anti_right S r (bop_right S). 
Proof. intros S r [s Ps]. 
       exists (s, s); compute. assumption. 
Defined. 

