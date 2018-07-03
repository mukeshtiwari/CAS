Require Import CAS.verify.bs_proofs_to_certs.
Require Import CAS.code.cas.bs.and_or. 
Require Import CAS.a_code.a_cas.bs.and_or.

Theorem correct_distributive_lattice_and_or :
      distributive_lattice_and_or = A2C_distributive_lattice bool (A_distributive_lattice_and_or). 
Proof. compute. reflexivity. Qed. 

