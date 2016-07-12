Require Import Coq.Bool.Bool.    
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 


Lemma brel2_conjunction_congruence : 
         ∀ (S T: Type) (rS : brel S) (rT : brel T) (r2 : brel S),  
            brel2_congruence S eq r1  → 
            brel2_congruence S eq r2  → 
               brel2_congruence S eq (brel2_conjunction S T r1 r2). 
Proof. unfold brel_congruence, brel_conjunction. 
       intros S eq r1 r2 C1 C2 s t u v H K. 
       rewrite (C1 _ _ _ _ H K). rewrite (C2 _ _ _ _ H K). 
       reflexivity. 
Defined.









