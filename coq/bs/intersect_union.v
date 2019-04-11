Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.base. 
Require Import CAS.coq.bs.union_intersect.
Require Import CAS.coq.bs.dual.

Section Theory.

  (* see CAS.coq.bs.union_intersect for theory *) 
  
End Theory.

Section ACAS.

Definition A_distributive_lattice_intersect_union (S : Type) (eqv : A_eqv S) : A_distributive_lattice (finite_set S)
               := A_distributive_lattice_dual _ (A_distributive_lattice_union_intersect S eqv). 
End ACAS.

Section CAS.

Definition distributive_lattice_intersect_union (S : Type) (eqv : @eqv S) : @distributive_lattice (finite_set S) 
               := distributive_lattice_dual (@distributive_lattice_union_intersect S eqv).   

End CAS.

Section Verify.



Theorem correct_distributive_lattice_intersect_union : ∀ (S : Type) (eqv: A_eqv S), 
    distributive_lattice_intersect_union S (A2C_eqv S eqv)
    =
    A2C_distributive_lattice _ (A_distributive_lattice_intersect_union S eqv). 
Proof. intros S eqv. unfold distributive_lattice_intersect_union, A_distributive_lattice_intersect_union.
       rewrite correct_distributive_lattice_union_intersect.
       reflexivity.
Qed. 


End Verify.   
  