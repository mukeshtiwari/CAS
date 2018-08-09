Require Import CAS.code.basic_types.
Require Import CAS.code.brel. 
Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.           
Require Import CAS.code.cas.eqv.list. 
Require Import CAS.a_code.a_cas.eqv.list. 
Require Import CAS.verify.eqv_proofs_to_certs.


Theorem correct_eqv_list : ∀ (S : Type) (E : A_eqv S),  
         eqv_list (A2C_eqv S E) = A2C_eqv (list S) (A_eqv_list S E). 
Proof. intros S E. destruct E. compute . reflexivity. Qed. 
