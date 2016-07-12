Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.bop_product. 

(*

What is really the natural * associated with "A left_sum B" ? 

it is 

     (a, b) |> inl c = inl (a *_A c) 
     (a, b) |> inr c = inr (b *_B c) 
      
        <b> |> inl c = inr b 
        <b> |> inr c = inr (b *_B c) 

*) 


Lemma bops_left_sum_right_sum_left_distributive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_reflexive S rS → 
      brel_reflexive T rT → 
      brel_symmetric T rT → 
      brel_transitive T rT → 
      bop_idempotent T rT addT → 
      bop_commutative T rT addT → 
      bops_left_absorption T rT addT mulT → 
      bop_left_distributive S rS addS mulS → 
      bop_left_distributive T rT addT mulT → 
         bop_left_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_right_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT refS refT symT transT idemT commT absT ldS ldT 
          [s1 | t1] [s2 | t2] [s3 | t3]; compute; auto. 
       assert (fact1 := commT t1 (mulT t1 t2)). 
       assert (fact2 := absT t1 t2). 
       assert (fact3 := transT _ _ _ fact2 fact1). 
       assumption.
Qed. 

Lemma bops_left_sum_right_sum_not_left_distributive_v1 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bop_not_left_distributive S rS addS mulS → 
         bop_not_left_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_right_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [ [s1 [s2 s3]] P]. 
       exists (inl s1, (inl s2, inl s3)). compute.  assumption. 
Defined. 

Lemma bops_left_sum_right_sum_not_left_distributive_v2 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bop_not_left_distributive T rT addT mulT → 
         bop_not_left_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_right_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [ [t1 [t2 t3]] P]. 
       exists (inr t1, (inr t2, inr t3)). compute.  assumption. 
Defined. 


Lemma bops_left_sum_right_sum_not_left_distributive_v3 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (s : S), 
      brel_symmetric T rT → 
      bop_not_idempotent T rT addT → 
         bop_not_left_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_right_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT s symT [t P].
       exists (inr t, (inl s, inl s)). compute.  
       apply (brel_symmetric_implies_dual _ _ symT). assumption. 
Defined. 


Lemma bops_left_sum_right_sum_not_left_distributive_v4 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (s : S), 
      brel_symmetric T rT → 
      brel_transitive T rT → 
      bop_commutative T rT addT → 
      bops_not_left_absorption T rT addT mulT → 
         bop_not_left_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_right_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT s symT transT commT [ [t1 t2] P].
       exists (inr t1, (inr t2, inl s)). compute.
       assert (fact1 := commT t1 (mulT t1 t2)). 
       apply (brel_symmetric_implies_dual _ _ symT) in P. 
       assert (fact2 := brel_transititivity_implies_dual _ _ transT _ _ _ fact1 P). 
       apply (brel_symmetric_implies_dual _ _ symT).
       assumption. 
Defined. 


Lemma bops_left_sum_right_sum_right_distributive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_reflexive S rS → 
      brel_reflexive T rT → 
      brel_symmetric T rT → 
      brel_transitive T rT → 
      bop_idempotent T rT addT → 
      bop_commutative T rT addT → 
      bops_right_absorption T rT addT mulT → 
      bop_right_distributive S rS addS mulS → 
      bop_right_distributive T rT addT mulT → 
         bop_right_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_right_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT refS refT symT transT idemT commT absT ldS ldT 
          [s1 | t1] [s2 | t2] [s3 | t3]; compute; auto. 
       assert (fact1 := commT t1 (mulT t2 t1)). 
       assert (fact2 := absT t1 t2). 
       assert (fact3 := transT _ _ _ fact2 fact1). 
       assumption.
Qed. 

Lemma bops_left_sum_right_sum_not_right_distributive_v1 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_right_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [ [s1 [s2 s3]] P]. 
       exists (inl s1, (inl s2, inl s3)). compute.  assumption. 
Defined. 

Lemma bops_left_sum_right_sum_not_right_distributive_v2 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bop_not_right_distributive T rT addT mulT → 
         bop_not_right_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_right_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [ [t1 [t2 t3]] P]. 
       exists (inr t1, (inr t2, inr t3)). compute.  assumption. 
Defined. 


Lemma bops_left_sum_right_sum_not_right_distributive_v3 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (s : S), 
      brel_symmetric T rT → 
      bop_not_idempotent T rT addT → 
         bop_not_right_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_right_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT s symT [t P].
       exists (inr t, (inl s, inl s)). compute.  
       apply (brel_symmetric_implies_dual _ _ symT). assumption. 
Defined. 

Lemma bops_left_sum_right_sum_not_right_distributive_v4 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (s : S), 
      brel_symmetric T rT → 
      brel_transitive T rT → 
      bop_commutative T rT addT → 
      bops_not_right_absorption T rT addT mulT → 
         bop_not_right_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_right_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT s symT transT commT [ [t1 t2] P].
       exists (inr t1, (inr t2, inl s)). compute.
       assert (fact1 := commT t1 (mulT t2 t1)). 
       apply (brel_symmetric_implies_dual _ _ symT) in P. 
       assert (fact2 := brel_transititivity_implies_dual _ _ transT _ _ _ fact1 P). 
       apply (brel_symmetric_implies_dual _ _ symT).
       assumption. 
Defined. 


(*

Lemma bops_left_sum_right_sum_not_left_constant_ : 
   ∀ (S T: Type) (rS : brel S) (rT : brel T) 
        (addS  mulS : binary_op S) (addT mulT : binary_op T) (s : S) (t : T), 
         bops_not_left_constant (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_right_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT s t. 
       exists (inl s, (inr t, inl s)); compute. reflexivity. 
Defined.      


Lemma bops_left_sum_right_sum_not_right_constant_ : 
   ∀ (S T: Type) (rS : brel S) (rT : brel T) 
        (addS  mulS : binary_op S) (addT mulT : binary_op T) (s : S) (t : T), 
         bops_not_right_constant (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_right_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT s t. 
       exists (inl s, (inr t, inl s)); compute. reflexivity. 
Defined.      
  *)      


