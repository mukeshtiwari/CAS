Require Import CAS.code.basic_types.
Require Import CAS.code.brel. 
Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.           
Require Import CAS.code.cas.eqv.list. 
Require Import CAS.a_code.a_cas.eqv.list. 
Require Import CAS.verify.eqv_proofs_to_certs.

(*
Lemma correct_eqv_certs_brel_list : 
      ∀ (S : Type) (r : brel S) (P : eqv_proofs S r), 
       eqv_certs_brel_list (P2C_eqv S r P) 
       = 
       P2C_eqv (list S) (brel_list r) (eqv_proofs_brel_list S r P). 
Proof. intros S r P. destruct P. 
       destruct A_eqv_nontrivial. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. 
       compute. reflexivity. 
Defined. 
*)

Theorem correct_eqv_list : ∀ (S : Type) (E : A_eqv S),  
         eqv_list (A2C_eqv S E) = A2C_eqv (list S) (A_eqv_list S E). 
Proof. intros S E. destruct E. compute . reflexivity. Qed. 
