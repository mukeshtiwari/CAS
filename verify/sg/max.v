
Require Import CAS.verify.sg_proofs_to_certs.
Require Import CAS.code.cas.sg.max. 
Require Import CAS.a_code.a_cas.sg.max.

Theorem correct_sg_CS_max : sg_CS_max = A2C_sg_CS nat (A_sg_CS_max). 
Proof. compute. reflexivity. Qed. 

(*
Theorem correct_sg_min : sg_min = A2C_sg nat (A_sg_min). 
Proof. compute. reflexivity. Qed. 

*) 