Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.

Require Import CAS.coq.eqv.bool.
Require Import CAS.coq.bs.and_or.
Require Import CAS.coq.bs.dual.

Section Theory.
End Theory.  

Section ACAS.

Definition A_selective_distributive_lattice_or_and : A_selective_distributive_lattice bool :=
    A_selective_distributive_lattice_dual bool A_selective_distributive_lattice_and_or.   

End ACAS.

Section AMCAS.

Definition A_mcas_bs_or_and := A_BS_selective_distributive_lattice _   A_selective_distributive_lattice_or_and.
  
End AMCAS.   


Section CAS.

Definition selective_distributive_lattice_or_and : @selective_distributive_lattice bool :=
    selective_distributive_lattice_dual selective_distributive_lattice_and_or.   

End CAS.

Section MCAS.

Definition mcas_bs_or_and := BS_selective_distributive_lattice selective_distributive_lattice_or_and.
  
End MCAS.   


Section Verify.
Theorem correct_selective_distributive_lattice_or_and : 
   selective_distributive_lattice_or_and = A2C_selective_distributive_lattice bool (A_selective_distributive_lattice_or_and). 
Proof. compute. reflexivity. Qed. 

Theorem correct_mcas_bs_and_or : mcas_bs_or_and = A2C_mcas_bs bool A_mcas_bs_or_and.
Proof. compute. reflexivity. Qed. 

 
End Verify.   
  
