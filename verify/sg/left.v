Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.bop.

Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.
Require Import CAS.code.sg_certificates. 
Require Import CAS.code.sg_cert_records. 
Require Import CAS.verify.eqv_proofs_to_certs.
Require Import CAS.verify.sg_proofs_to_certs.

Require Import CAS.code.cas.sg.left.
Require Import CAS.a_code.a_cas.sg.left. 
Require Import CAS.theory.brel_properties. (* for brel_not_trivial *) 

Lemma correct_sg_certs_left : 
      ∀ (S : Type) (r : brel S) (s : S) (f : S -> S) (Pf : brel_not_trivial S r f) (P : eqv_proofs S r), 
       sg_certs_left s f 
       = 
       P2C_sg S r (@bop_left S) (sg_proofs_left S r s f Pf P). 
Proof. intros S r s f Pf P. compute. reflexivity. Defined. 


Theorem correct_sg_left :
      ∀ (S : Type) (eS : A_eqv S), 
         sg_left (A2C_eqv S eS) 
         = 
         A2C_sg S (A_sg_left S eS). 
Proof. intros S eS. unfold sg_left, A2C_sg; simpl. 
       rewrite <- correct_sg_certs_left.  
       reflexivity. 
Qed. 
