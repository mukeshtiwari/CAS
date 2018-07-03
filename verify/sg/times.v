Require Import CAS.verify.sg_proofs_to_certs.
Require Import CAS.a_code.a_cas.sg.times.
Require Import CAS.code.cas.sg.times. 

Theorem correct_sg_C_times : sg_C_times = A2C_sg_C nat (A_sg_C_times). 
Proof. compute. reflexivity. Qed.

(*
Theorem correct_sg_times : sg_times = A2C_sg nat (A_sg_times). 
Proof. compute. reflexivity. Qed. 

*) 
