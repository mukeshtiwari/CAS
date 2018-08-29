Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.eqv.nat.
Require Import CAS.coq.bs.min_max.
Require Import CAS.coq.bs.dual.

Section Theory.
End Theory.  

Section ACAS.
  Definition A_selective_distributive_lattice_max_min : A_selective_distributive_lattice nat :=
    A_selective_distributive_lattice_dual nat A_selective_distributive_lattice_min_max.   
End ACAS.


Section CAS.
  Definition selective_distributive_lattice_max_min : @selective_distributive_lattice nat :=
    selective_distributive_lattice_dual selective_distributive_lattice_min_max.   
End CAS.

Section Verify.
Theorem correct_selective_distributive_lattice_max_min : 
   selective_distributive_lattice_max_min = A2C_selective_distributive_lattice nat (A_selective_distributive_lattice_max_min). 
Proof. compute. reflexivity. Qed. 
  
 
End Verify.   
  