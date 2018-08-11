Require Import CAS.coq.common.base. 
Require Import CAS.coq.eqv.bool.
Require Import CAS.coq.bs.and_or.
Require Import CAS.coq.bs.dual.

Section Theory.
End Theory.  

Section ACAS.
Definition A_distributive_lattice_or_and : A_distributive_lattice bool := A_distributive_lattice_dual bool A_distributive_lattice_and_or.   
End ACAS.


Section CAS.
Definition distributive_lattice_or_and : @distributive_lattice bool := distributive_lattice_dual distributive_lattice_and_or.   
End CAS.

Section Verify.
Theorem correct_distributive_lattice_or_and : 
   distributive_lattice_or_and = A2C_distributive_lattice bool (A_distributive_lattice_or_and). 
Proof. compute. reflexivity. Qed. 
  
 
End Verify.   
  