Require Import CAS.code.basic_types.
Require Import CAS.code.brel. 
Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.           
Require Import CAS.code.cas.eqv.add_constant. 
Require Import CAS.a_code.a_cas.eqv.add_constant. 
Require Import CAS.verify.eqv_proofs_to_certs.

(*
Lemma correct_eqv_certs_add_constant : 
      ∀ (S : Type) (r : brel S) (c : cas_constant) (P : eqv_proofs S r), 
       eqv_certs_add_constant c (P2C_eqv S r P) 
       = 
       P2C_eqv (with_constant S) (brel_add_constant r c) (eqv_proofs_add_constant S r c P). 
Proof. intros S r c P. destruct P. 
       unfold eqv_certs_add_constant, eqv_proofs_add_constant, P2C_eqv; simpl. 
       destruct A_eqv_nontrivial. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. 
       compute. reflexivity. 
Defined. 
*) 
Theorem correct_eqv_add_constant : ∀ (S : Type) (c : cas_constant) (E : A_eqv S),  
    eqv_add_constant (A2C_eqv S E) c = A2C_eqv (with_constant S) (A_eqv_add_constant S E c).
Proof. intros S c E. destruct E, A_eqv_proofs. compute. reflexivity. Qed. 
