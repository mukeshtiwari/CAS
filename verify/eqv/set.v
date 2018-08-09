Require Import CAS.code.basic_types.
Require Import CAS.code.brel. 
Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.           
Require Import CAS.code.cas.eqv.set. 
Require Import CAS.a_code.a_cas.eqv.set. 
Require Import CAS.verify.eqv_proofs_to_certs.

Theorem correct_eqv_set : ∀ (S : Type) (E : A_eqv S),  
    eqv_set (A2C_eqv S E) = A2C_eqv (finite_set S) (A_eqv_set S E).
Proof. intros S E. destruct E, A_eqv_proofs. compute. reflexivity. Qed. 

