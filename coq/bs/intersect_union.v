
Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.base. 
Require Import CAS.coq.bs.union_intersect.
Require Import CAS.coq.bs.dual.

Section Theory.

  (* theory is in CAS.coq.bs.union_intersect *) 

End Theory.

Section ACAS.

Definition A_distributive_lattice_intersect_union (S : Type) (eqv : A_eqv S) (c : cas_constant) : A_distributive_lattice (with_constant (finite_set S)) 
               := A_distributive_lattice_dual _ (A_distributive_lattice_union_intersect S eqv c). 
End ACAS.

Section CAS.

Definition distributive_lattice_intersect_union (S : Type) (eqv : @eqv S) (c : cas_constant) : @distributive_lattice (with_constant (finite_set S)) 
               := distributive_lattice_dual (@distributive_lattice_union_intersect S eqv c).   

End CAS.

Section Verify.



Theorem correct_distributive_lattice_intersect_union : ∀ (S : Type) (eqv: A_eqv S) (c : cas_constant), 
    distributive_lattice_intersect_union S (A2C_eqv S eqv) c 
    =
    A2C_distributive_lattice _ (A_distributive_lattice_intersect_union S eqv c). 
Proof. intros S eqv c. unfold distributive_lattice_intersect_union, A_distributive_lattice_intersect_union.
       rewrite correct_distributive_lattice_union_intersect.
       reflexivity.
Qed. 


End Verify.   
  