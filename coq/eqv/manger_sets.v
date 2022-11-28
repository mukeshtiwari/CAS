Require Import Coq.Lists.List.
Require Import CAS.coq.common.compute.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.trivial. 

Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.product.

Require Import CAS.coq.uop.properties.

Section Computation.

(*
• Phase 1. All pairs from X with equal active components are merged
into a single pair whose active component is the one found in the
original pairs and passive component is the join of passive components
from the original pairs. For instance, if X contains altogether three
pairs with a given x ∈ P , i.e., (x, x1 ), (x, x2 ) and (x, x3 ), then they are
replaced with a single pair (x, x1 ∨ x2 ∨ x3 ). Note that after phase 1
all pairs in X have distinct active components.

• Phase 2. All pairs from X that are dominated in X with respect
to their active components are deleted from X. For instance, if X
contains two pairs (x, x') and (y, y') such that x ≺ y, then the pair
(x, x') is deleted. In other words, phase 2 leaves in X only those pairs
that are efficient according to their active component.

TGG22: Note that Manger's order is the dual of our left order. 
*)   

(* 
  A = type of active component
  P = type of passive component
*)   
Fixpoint manger_merge_sets
           {A P : Type}
           (eqA : brel A)
           (addP : binary_op P)
           (Y : finite_set (A * P))
           (p1 : A * P) :=
  match Y with
  | nil => p1 :: nil
  | p2 :: Y' =>
    match p1, p2 with
    | (s1, t1), (s2, t2) =>
      if eqA s1 s2
      then (s1, addP t1 t2) :: Y' 
      else p2 :: (manger_merge_sets eqA addP Y' p1) 
    end 
  end.

Definition manger_phase_1_auxiliary 
          {A P : Type}
          (eqA : brel A)
          (addP : binary_op P) 
          (Y : finite_set (A * P))
          (X : finite_set (A * P))  : finite_set (A * P) :=
  fold_left (manger_merge_sets eqA addP) X Y.

Definition uop_manger_phase_1 
          {A P : Type}
          (eqA : brel A)
          (addP : binary_op P) 
          (X : finite_set (A * P))  : finite_set (A * P) :=
  manger_phase_1_auxiliary  eqA addP nil X.   

Definition equal_manger_phase_1 
          {A P : Type}
          (eqA : brel A)
          (eqP : brel P)          
          (addP : binary_op P) : brel (finite_set (A * P)) :=
  λ X Z, brel_set (brel_product eqA eqP)
                  (uop_manger_phase_1 eqA addP X)
                  (uop_manger_phase_1 eqA addP Z). 

Definition manger_pre_order
           {A P : Type}
           (lteA : brel A) : brel (A * P)
  := brel_product lteA (@brel_trivial P). 

Definition uop_manger_phase_2
           {A P : Type} (lteA : brel A) : unary_op (finite_set (A * P))          
  := uop_minset (manger_pre_order lteA). 


Definition equal_manger
          {A P : Type}
          (eqA lteA : brel A)
          (eqP : brel P)          
          (addP : binary_op P) : brel (finite_set (A * P)) :=
  λ X Z, equal_manger_phase_1 eqA eqP addP 
                  (@uop_manger_phase_2 A P lteA X)
                  (@uop_manger_phase_2 A P lteA Z).

End Computation. 

Section Theory.

Variables (A P : Type) 
          (eqA lteA : brel A)
          (eqP : brel P)          
          (addP : binary_op P).  

Local Notation "[P2]" := (uop_manger_phase_2 lteA ).
Local Notation "[EM]" := (equal_manger eqA lteA eqP addP).

Lemma uop_manger_phase_2_is_idempotent : uop_idempotent _ [EM] [P2]. 
Admitted. 

(* properties of [EM *) 
Lemma equal_manger_congruence : brel_congruence _ [EM] [EM].
Admitted.

Lemma equal_manger_reflexive : brel_reflexive _ [EM].
Admitted.

Lemma equal_manger_symmetric : brel_symmetric _ [EM].
Admitted.

Lemma equal_manger_transitive : brel_symmetric _ [EM].
Admitted.


  
End Theory.   
