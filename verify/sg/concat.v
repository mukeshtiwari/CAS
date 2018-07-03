Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.bop.

Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.
Require Import CAS.code.sg_certificates. 
Require Import CAS.code.sg_cert_records. 
Require Import CAS.verify.eqv_proofs_to_certs.
Require Import CAS.verify.sg_proofs_to_certs.

Require Import CAS.verify.eqv.list. 
Require Import CAS.code.cas.sg.concat.
Require Import CAS.a_code.a_cas.sg.concat.
Require Import CAS.theory.brel_properties. (* for brel_not_trivial *) 


Lemma correct_sg_certs_concat : 
      ∀ (S : Type) (r : brel S) (s : S) (f : S -> S) (Pf : brel_not_trivial S r f) (P : eqv_proofs S r), 
       sg_certs_concat s f 
       = 
       P2C_sg (list S) (brel_list r) (@bop_concat S) (sg_proofs_concat S r s f Pf P). 
Proof. intros S r s f Pf P. destruct P. compute. reflexivity. Defined. 


Theorem correct_sg_concat : ∀ (S : Type) (eS : A_eqv S), 
         sg_concat (A2C_eqv S eS) 
         = 
         A2C_sg (list S) (A_sg_concat S eS). 
Proof. intros S eS. unfold sg_concat, A2C_sg. simpl. 
       rewrite correct_eqv_list. 
       rewrite <- correct_sg_certs_concat. 
       reflexivity. 
Qed. 
