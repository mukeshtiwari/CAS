Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.cas.eqv.bool. 
Require Import CAS.a_code.a_cas.eqv.bool. 
Require Import CAS.verify.eqv_proofs_to_certs.


Theorem correct_eqv_bool : eqv_eq_bool = A2C_eqv bool (A_eqv_bool). 
Proof. compute. reflexivity. Qed. 
