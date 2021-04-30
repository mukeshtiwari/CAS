Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.

Require Import CAS.coq.bs.union_intersect.
Require Import CAS.coq.bs.dual.

Section Theory.

  (* see CAS.coq.bs.union_intersect for theory *) 
  
End Theory.

Section ACAS.

Definition A_distributive_prelattice_intersect_union (S : Type) (eqv : A_eqv S) : A_distributive_prelattice (finite_set S)
               := A_distributive_prelattice_dual _ (A_distributive_prelattice_union_intersect S eqv). 
End ACAS.

Section CAS.

Definition distributive_prelattice_intersect_union (S : Type) (eqv : @eqv S) : @distributive_prelattice (finite_set S) 
               := distributive_prelattice_dual (@distributive_prelattice_union_intersect S eqv).   

End CAS.

Section Verify.



Theorem correct_distributive_prelattice_intersect_union : ∀ (S : Type) (eqv: A_eqv S), 
    distributive_prelattice_intersect_union S (A2C_eqv S eqv)
    =
    A2C_distributive_prelattice _ (A_distributive_prelattice_intersect_union S eqv). 
Proof. intros S eqv.  unfold distributive_prelattice_intersect_union, A_distributive_prelattice_intersect_union.
       rewrite <- correct_distributive_prelattice_dual.
       rewrite correct_distributive_prelattice_union_intersect.       
       reflexivity.
Qed. 


End Verify.   
  