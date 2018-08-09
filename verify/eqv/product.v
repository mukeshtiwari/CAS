Require Import CAS.code.basic_types.
Require Import CAS.code.brel. 
Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.           
Require Import CAS.code.cas.eqv.product. 
Require Import CAS.a_code.a_cas.eqv.product. 
Require Import CAS.verify.eqv_proofs_to_certs.

Theorem correct_eqv_product :
      ∀ (S T : Type) (eS : A_eqv S) (eT : A_eqv T), 
         eqv_product (A2C_eqv S eS) (A2C_eqv T eT)
         = 
         A2C_eqv (S * T) (A_eqv_product S T eS eT). 
Proof. intros S T eS eT. destruct eS; destruct eT. compute. reflexivity. Qed. 

