Require Import CAS.verify.sg_proofs_to_certs.
Require Import CAS.code.cas.sg.min. 
Require Import CAS.a_code.a_cas.sg.min.

Theorem correct_sg_CS_min : sg_CS_min = A2C_sg_CS nat (A_sg_CS_min). 
Proof. compute. reflexivity. Qed. 

(*
Theorem correct_sg_max : sg_max = A2C_sg nat (A_sg_max). 
Proof. compute. reflexivity. Qed. 
*) 
