Require Import Coq.Arith.Arith.     
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel_conjunction. 
Require Import CAS.theory.brel_dual. 
Require Import CAS.theory.brel_reverse. 


Lemma brel_strictify_irreflexive_v1 : ∀ (S : Type) (r : brel S), 
          brel_reflexive S r -> brel_irreflexive S (brel_strictify S r).  
Proof. intros S r H. 
       unfold brel_strictify. 
       apply brel_conjunction_irreflexive. 
       right. 
       apply brel_dual_irreflexive. 
       apply brel_reverse_reflexive. 
       assumption. 
Defined. 

Lemma brel_strictify_irreflexive_v2 : ∀ (S : Type) (r : brel S), 
          brel_irreflexive S r -> brel_irreflexive S (brel_strictify S r).  
Proof. intros S r H. 
       unfold brel_strictify. 
       apply brel_conjunction_irreflexive. 
       left. 
       assumption. 
Defined. 


Lemma brel_strictify_irreflexive : ∀ (S : Type) (r : brel S), 
       ((brel_reflexive S r) + (brel_irreflexive S r)) -> brel_irreflexive S (brel_strictify S r).  
Proof. intros S r [H | H]. 
       apply brel_strictify_irreflexive_v1; auto. 
       apply brel_strictify_irreflexive_v2; auto. 
Qed.  

Lemma brel_strictify_congruence : ∀ (S : Type) (r1 : brel S) (r2 : brel S), 
         brel_congruence S r1 r2 -> brel_congruence S r1 (brel_strictify S r2). 
Proof. intros S r1 r2 H. 
       unfold brel_strictify. 
       apply brel_conjunction_congruence; auto. 
       apply brel_dual_congruence.
       apply brel_reverse_congruence.  
       assumption. 
Defined. 




