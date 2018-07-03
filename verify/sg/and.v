Require Import CAS.verify.sg_proofs_to_certs.
Require Import CAS.code.cas.sg.and. 
Require Import CAS.a_code.a_cas.sg.and.

Theorem correct_sg_CS_and : sg_CS_and = A2C_sg_CS bool (A_sg_CS_and). 
Proof. compute. reflexivity. Qed. 

(*
Theorem correct_sg_and : sg_and = A2C_sg bool (A_sg_and). 
Proof. compute. reflexivity. Qed. 
*) 