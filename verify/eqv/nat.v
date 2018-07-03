Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.cas.eqv.nat. 
Require Import CAS.a_code.a_cas.eqv.nat. 
Require Import CAS.verify.eqv_proofs_to_certs.

(*
Theorem correct_eqv_certs_nat : eqv_certs_eq_nat = P2C_eqv nat brel_eq_nat (eqv_proofs_eq_nat). 
Proof. compute. reflexivity. Qed. 
*)
Theorem correct_eqv_nat : eqv_eq_nat = A2C_eqv nat (A_eqv_nat). 
Proof. compute. reflexivity. Qed. 
