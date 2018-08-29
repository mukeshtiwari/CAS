Require Import CAS.coq.common.base. 
Require Import CAS.coq.eqv.bool.
Require Import CAS.coq.bs.and_or.
Require Import CAS.coq.bs.dual.

Section Theory.
End Theory.  

Section ACAS.
  Definition A_selective_distributive_lattice_or_and : A_selective_distributive_lattice bool :=
    A_selective_distributive_lattice_dual bool A_selective_distributive_lattice_and_or.   
End ACAS.


Section CAS.
  Definition selective_distributive_lattice_or_and : @selective_distributive_lattice bool :=
    selective_distributive_lattice_dual selective_distributive_lattice_and_or.   
End CAS.

Section Verify.
Theorem correct_selective_distributive_lattice_or_and : 
   selective_distributive_lattice_or_and = A2C_selective_distributive_lattice bool (A_selective_distributive_lattice_or_and). 
Proof. compute. reflexivity. Qed. 
  
 
End Verify.   
  