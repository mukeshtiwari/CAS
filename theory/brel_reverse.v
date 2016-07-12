Require Import Coq.Arith.Arith.     
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 

Lemma brel_reverse_irreflexive : ∀ (S : Type) (r : brel S), 
          brel_irreflexive S r -> brel_irreflexive S (brel_reverse S r).  
Proof. unfold brel_reflexive, brel_irreflexive, brel_reverse. intros S r H s. 
       rewrite (H s). compute. reflexivity. 
Defined. 


Lemma brel_reverse_reflexive : ∀ (S : Type) (r : brel S), 
          brel_reflexive S r -> brel_reflexive S (brel_reverse S r).  
Proof. unfold brel_reflexive, brel_irreflexive, brel_reverse. intros S r H s. 
       rewrite (H s). compute. reflexivity. 
Defined. 

Lemma brel_reverse_symmetric : ∀ (S : Type) (r : brel S), 
          brel_symmetric S r -> brel_symmetric S (brel_reverse S r).  
Proof. unfold brel_symmetric, brel_reverse. intros S r symS s t J. 
       apply symS. assumption. 
Defined. 


Lemma brel_reverse_congruence : ∀ (S : Type) (r1 : brel S) (r2 : brel S), 
         brel_congruence S r1 r2 -> brel_congruence S r1 (brel_reverse S r2). 
Proof. unfold brel_congruence, brel_reverse. 
       intros S r1 r2 cong s t u v H1 H2.
       assert (fact2 :=  cong _ _ _ _ H2 H1). assumption. 
Defined. 




