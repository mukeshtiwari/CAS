Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 

Lemma bop_add_ann_congruence : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
      brel_reflexive S rS → bop_congruence S rS bS → 
        bop_congruence (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c). 
Proof. 
   unfold bop_congruence. intros S rS c bS refS congS 
   [s1 | t1] [s2 | t2] [s3 | t3] [s4 | t4]; simpl; intros H1 H2;auto. 
Qed. 

Lemma bop_add_ann_associative : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
      brel_reflexive S rS → bop_associative S rS bS → 
      bop_associative (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c). 
Proof. intros S rS c bS refS congS [s1 | t1] [s2 | t2] [s3 | t3]; simpl; auto. Qed. 

Lemma bop_add_ann_idempotent : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
      bop_idempotent S rS bS → 
      bop_idempotent (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c). 
Proof. intros S rS c bS idemS [s1 | t1]; simpl; auto. Qed. 

Lemma bop_add_ann_not_idempotent : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
      bop_not_idempotent S rS bS → 
      bop_not_idempotent (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c). 
Proof. intros S rS c bS [s P]. exists (inr _ s). simpl. assumption. Defined. 


Lemma bop_add_ann_commutative : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
      brel_reflexive S rS → 
      bop_commutative S rS bS → 
         bop_commutative (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c). 
Proof. intros S rS c bS refS commS [s1 | t1] [s2 | t2]; simpl; auto. Qed. 

Lemma bop_add_ann_not_commutative : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
      bop_not_commutative S rS bS → 
      bop_not_commutative (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c). 
Proof. intros S rS c bS [ [s t] P]. exists (inr _ s, inr _ t); simpl. assumption. Defined. 


Lemma bop_add_ann_selective : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
      brel_reflexive S rS → 
      bop_selective S rS bS → 
      bop_selective (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c). 
Proof. intros S rS c bS refS selS [s1 | t1] [s2 | t2]; simpl; auto. Qed. 
   

Lemma bop_add_ann_not_selective : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
      bop_not_selective S rS bS → 
         bop_not_selective (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c). 
Proof. intros S rS c bS [ [s1 s2] P]. exists (inr _ s1, inr _ s2). simpl. assumption. Defined. 



Lemma bop_add_ann_exists_ann : 
     ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
        brel_reflexive S rS → 
           bop_exists_ann (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c).
Proof. intros S rS c bS refS. exists (inl S c). intros [a | b]; compute; auto. Defined. 



Lemma bop_add_ann_exists_id : 
     ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
       brel_reflexive S rS -> 
       bop_exists_id S rS bS -> 
           bop_exists_id (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c).
Proof. intros S rS c bS refS [annS pS]. exists (inr _ annS). 
       intros [s | t]; compute; auto. 
Defined. 


Lemma bop_add_ann_not_exists_id : 
     ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
       brel_witness S rS ->   
       bop_not_exists_id S rS bS -> 
           bop_not_exists_id (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c).
Proof. intros S rS c bS [s sP] naS. intros [x | x].
       exists (inr _ s). compute; auto. 
       destruct (naS x) as [y D].  exists (inr _ y). compute. assumption. 
Defined. 


Lemma bop_add_ann_not_is_left : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S),
      brel_witness S rS ->   
      bop_not_is_left (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c). 
Proof. intros S rS c bS [s _]. exists (inr _ s, inl _ c). simpl. reflexivity. Defined. 

Lemma bop_add_ann_not_is_right : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
      brel_witness S rS ->   
      bop_not_is_right (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c). 
Proof. intros S rS c bS [s _]. exists (inl _ c, inr _ s). simpl. reflexivity. Defined. 


Lemma bop_add_ann_not_left_cancellative : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b : binary_op S), 
     brel_nontrivial S r -> 
      bop_not_left_cancellative (with_constant S) (brel_add_constant S r c) (bop_add_ann S b c).
Proof. intros S r c b [[s Ps] [f Pf]]. 
       exists (inl _ c, (inr _ s, inr _ (f s))); simpl.
       destruct (Pf s) as [L R]. split; auto.
Defined. 

Lemma bop_add_ann_not_right_cancellative : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b : binary_op S), 
     brel_nontrivial S r -> 
      bop_not_right_cancellative (with_constant S) (brel_add_constant S r c) (bop_add_ann S b c).
Proof. intros S r c b [[s Ps] [f Pf]]. 
       exists (inl _ c, (inr _ s, inr _ (f s))); simpl.
       destruct (Pf s) as [L R]. split; auto.
Defined. 

Lemma bop_add_ann_not_left_constant : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b : binary_op S), 
     brel_witness S r -> 
      bop_not_left_constant (with_constant S) (brel_add_constant S r c) (bop_add_ann S b c).
Proof. intros S r c b [s Ps]. 
       exists (inr _ s, (inr _ s, inl _ c)); simpl. reflexivity. 
Defined. 


Lemma bop_add_ann_not_right_constant : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b : binary_op S), 
     brel_witness S r -> 
      bop_not_right_constant (with_constant S) (brel_add_constant S r c) (bop_add_ann S b c).
Proof. intros S r c b [s Ps]. 
       exists (inr _ s, (inr _ s, inl _ c)); simpl. reflexivity. 
Defined. 


Lemma bop_add_ann_not_anti_left : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b : binary_op S), 
     brel_witness S r -> 
        bop_not_anti_left (with_constant S) (brel_add_constant S r c) (bop_add_ann S b c).
Proof. intros S r c b [s Ps]. unfold bop_not_anti_left. 
       exists (inl c, inr s); simpl. reflexivity. 
Defined. 


Lemma bop_add_ann_not_anti_right : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b : binary_op S), 
     brel_witness S r -> 
        bop_not_anti_right (with_constant S) (brel_add_constant S r c) (bop_add_ann S b c).
Proof. intros S r c b [s Ps]. unfold bop_not_anti_right. 
       exists (inl c, inr s); simpl. reflexivity. 
Defined. 






