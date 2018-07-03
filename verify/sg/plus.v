Require Import CAS.verify.sg_proofs_to_certs.
Require Import CAS.code.cas.sg.plus. 
Require Import CAS.a_code.a_cas.sg.plus.

Theorem correct_sg_CK_plus : sg_CK_plus = A2C_sg_CK nat (A_sg_CK_plus). 
Proof. compute. reflexivity. Qed. 

(*
Theorem correct_sg_plus : sg_plus = A2C_sg nat (A_sg_plus). 
Proof. compute. reflexivity. Qed. 

*) 