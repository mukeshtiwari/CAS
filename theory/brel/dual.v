Require Import Coq.Arith.Arith.     
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 

Lemma brel_dual_irreflexive : ∀ (S : Type) (r : brel S), 
          brel_reflexive S r -> brel_irreflexive S (brel_dual S r).  
Proof. unfold brel_reflexive, brel_irreflexive, brel_dual. intros S r H s. 
       rewrite (H s). compute. reflexivity. 
Defined. 


Lemma brel_dual_reflexive : ∀ (S : Type) (r : brel S), 
          brel_irreflexive S r -> brel_reflexive S (brel_dual S r).  
Proof. unfold brel_reflexive, brel_irreflexive, brel_dual. intros S r H s. 
       rewrite (H s). compute. reflexivity. 
Defined. 

Lemma brel_dual_symmetric : ∀ (S : Type) (r : brel S), 
          brel_symmetric S r -> brel_symmetric S (brel_dual S r).  
Proof. unfold brel_symmetric, brel_dual. intros S r symS s t J. 
       apply negb_true_elim in J. 
       rewrite (brel_symmetric_implies_dual S r symS _ _ J). 
       compute. reflexivity. 
Defined. 

Lemma brel_dual_asymmetric : ∀ (S : Type) (r : brel S), 
          (∀ s t : S, r s t = false → r t s = true) -> 
          brel_asymmetric S (brel_dual S r).  
Proof. unfold brel_asymmetric, brel_dual. intros S r K s t J. 
       case_eq(r t s); intro Q. 
          compute. reflexivity. 
          rewrite (K _ _ Q) in J. compute in J. discriminate. 
Defined. 


Lemma brel_dual_congruence : ∀ (S : Type) (r1 : brel S) (r2 : brel S), 
         brel_congruence S r1 r2 -> brel_congruence S r1 (brel_dual S r2). 
Proof. unfold brel_congruence, brel_dual. 
       intros S r1 r2 cong s t u v H1 H2.
       assert (fact1 :=  cong _ _ _ _ H1 H2). 
       case_eq(r2 s t); intro Q. 
          rewrite <- fact1. rewrite Q. reflexivity. 
          rewrite <- fact1. rewrite Q. reflexivity. 
Defined. 




