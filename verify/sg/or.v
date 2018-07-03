Require Import CAS.verify.sg_proofs_to_certs.
Require Import CAS.code.cas.sg.or. 
Require Import CAS.a_code.a_cas.sg.or.

Theorem correct_sg_CS_or : sg_CS_or = A2C_sg_CS bool (A_sg_CS_or). 
Proof. compute. reflexivity. Qed. 

(*
Theorem correct_sg_or : sg_or = A2C_sg bool (A_sg_or). 
Proof. compute. reflexivity. Qed. 
*) 