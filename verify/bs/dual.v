Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.bop.

Require Import CAS.code.bs_certificates. 
Require Import CAS.code.bs_cert_records.

Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.

Require Import CAS.code.cas.bs.dual.
Require Import CAS.a_code.a_cas.bs.dual. 

Require Import CAS.theory.bop_properties.
Require Import CAS.theory.bs_properties. 

Require Import CAS.verify.eqv_proofs_to_certs.
Require Import CAS.verify.sg_proofs_to_certs.
Require Import CAS.verify.bs_proofs_to_certs.

Lemma  correct_lattice_certs_dual : 
  ∀ (S : Type) (rS : brel S) (join meet : binary_op S) (latticeS : lattice_proofs S rS join meet), 
    
    P2C_lattice S rS meet join (lattice_proofs_dual S rS join meet latticeS)
    =
    lattice_certs_dual (P2C_lattice S rS join meet latticeS).
Proof. intros S rS join meet latticeS. 
       unfold lattice_certs_dual, lattice_proofs_dual, P2C_lattice; simpl. 
       destruct latticeS; simpl. destruct A_lattice_distributive_d, A_lattice_distributive_dual_d; simpl; 
       reflexivity.
Qed. 

Theorem correct_lattice_dual : ∀ (S : Type) (latticeS: A_lattice S), 
   lattice_dual (A2C_lattice S latticeS) 
   =
   A2C_lattice S (A_lattice_dual S latticeS). 
Proof. intros S latticeS. 
       unfold lattice_dual, A_lattice_dual, A2C_lattice; simpl. 
       rewrite correct_lattice_certs_dual. 
       reflexivity. 
Qed. 


Lemma  correct_distributive_lattice_certs_dual : 
  ∀ (S : Type) (rS : brel S) (join meet : binary_op S)
     (eqvS : eqv_proofs S rS) (pjoin : sg_CI_proofs S rS join) (pmeet : sg_CI_proofs S rS meet) 
     (dlp : distributive_lattice_proofs S rS join meet), 
    P2C_distributive_lattice S rS meet join (distributive_lattice_proofs_dual S rS join meet eqvS pjoin pmeet dlp)
    =
    distributive_lattice_certs_dual (P2C_distributive_lattice S rS join meet dlp).
Proof. intros S rS join meet eqvS pjoin pmeet dlp. compute. reflexivity. Qed.

Theorem correct_distributive_lattice_add_one : ∀ (S : Type) (distributive_latticeS: A_distributive_lattice S), 
   distributive_lattice_dual  (A2C_distributive_lattice S distributive_latticeS)  
   =
   A2C_distributive_lattice S (A_distributive_lattice_dual S distributive_latticeS). 
Proof. intros S distributive_latticeS. 
       unfold distributive_lattice_dual, A_distributive_lattice_dual, A2C_distributive_lattice; simpl. 
       rewrite correct_distributive_lattice_certs_dual. 
       reflexivity. 
Qed. 
