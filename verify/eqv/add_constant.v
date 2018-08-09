Require Import CAS.code.basic_types.
Require Import CAS.code.brel. 
Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.           
Require Import CAS.code.cas.eqv.add_constant. 
Require Import CAS.a_code.a_cas.eqv.add_constant. 
Require Import CAS.verify.eqv_proofs_to_certs.

Theorem correct_eqv_add_constant : ∀ (S : Type) (c : cas_constant) (E : A_eqv S),  
    eqv_add_constant (A2C_eqv S E) c = A2C_eqv (with_constant S) (A_eqv_add_constant S E c).
Proof. intros S c E. destruct E, A_eqv_proofs. compute. reflexivity. Qed. 

