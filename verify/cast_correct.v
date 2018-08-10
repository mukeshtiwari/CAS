Require Import CAS.code.basic_types. 
Require Import CAS.code.cef. 
Require Import CAS.code.certificates.
Require Import CAS.code.cert_records.
Require Import CAS.code.cas_records.
Require Import CAS.code.cast.
Require Import CAS.theory.facts. 

Require Import CAS.a_code.proof_records.     (* ~~ cert_records *) 
Require Import CAS.a_code.a_cas_records.     
Require Import CAS.a_code.a_cast.


(* upcasts *) 



(* downcasts *) 


Lemma correct_sg_C_certs_option_from_sg_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (sgS : sg_proofs S r b), 
       sg_C_certs_option_from_sg_certs S (P2C_sg S r b sgS)
       = 
       P2C_sg_C_option S r b (A_sg_C_proofs_option_from_sg_proofs S r b sgS). 
Proof. intros S r b sgS. destruct sgS. 
       unfold sg_C_certs_option_from_sg_certs, A_sg_C_proofs_option_from_sg_proofs, 
              P2C_sg, P2C_sg_C_option; simpl. 
       destruct A_sg_commutative_d as [C | [ [s1 s2] NC]]; unfold P2C_sg_C; simpl. reflexivity. 
       reflexivity. 
Defined. 

Theorem correct_sg_C_option_from_sg : ∀ (S : Type) (P : A_sg S),  
         sg_C_option_from_sg S (A2C_sg S P) = A2C_sg_C_option S (A_sg_C_option_from_sg S P). 
Proof. intros S P. destruct P. 
       unfold A2C_sg, A2C_sg_C_option, sg_C_option_from_sg, A_sg_C_option_from_sg. simpl.  
       unfold A2C_sg_C, option_map.  
       rewrite correct_sg_C_certs_option_from_sg_certs. 
       case (A_sg_C_proofs_option_from_sg_proofs S (A_eqv_eq S A_sg_eq) A_sg_bop); simpl. 
          intro s. reflexivity. 
          reflexivity. 
Defined. 


Lemma correct_sg_CI_certs_option_from_sg_C_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (sgS : sg_C_proofs S r b), 
       sg_CI_certs_option_from_sg_C_certs S (P2C_sg_C S r b sgS)
       = 
       P2C_sg_CI_option S r b (A_sg_CI_proofs_option_from_sg_C_proofs S r b sgS). 
Proof. intros S r b sgS. destruct sgS. 
       unfold sg_CI_certs_option_from_sg_C_certs, A_sg_CI_proofs_option_from_sg_C_proofs, 
              P2C_sg_C, P2C_sg_CI_option; simpl. 
       destruct A_sg_C_idempotent_d as [I | [s0 NI]]; 
       simpl; reflexivity. 
Defined. 

Theorem correct_sg_CI_option_from_sg_C : ∀ (S : Type) (P : A_sg_C S),  
        sg_CI_option_from_sg_C S (A2C_sg_C S P) = A2C_sg_CI_option S (A_sg_CI_option_from_sg_C S P). 
Proof. intros S P. destruct P. 
       unfold A2C_sg_C, A2C_sg_CI_option, sg_CI_option_from_sg_C, A_sg_CI_option_from_sg_C; simpl.  
       rewrite correct_sg_CI_certs_option_from_sg_C_certs. 
       case (A_sg_CI_proofs_option_from_sg_C_proofs S (A_eqv_eq S A_sg_C_eqv) A_sg_C_bop A_sg_C_proofs); simpl. 
          intro s. reflexivity. 
          reflexivity. 
Defined. 

Lemma correct_sg_CS_certs_option_from_sg_CI_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (sgS : sg_CI_proofs S r b), 
       sg_CS_certs_option_from_sg_CI_certs S (P2C_sg_CI S r b sgS)
       = 
       P2C_sg_CS_option S r b (A_sg_CS_proofs_option_from_sg_CI_proofs S r b sgS). 
Proof. intros S r b sgS. destruct sgS. 
       unfold sg_CS_certs_option_from_sg_CI_certs, A_sg_CS_proofs_option_from_sg_CI_proofs, 
              P2C_sg_CI, P2C_sg_CS_option; simpl. 
       destruct A_sg_CI_selective_d as [sel | [ [s1 s2] nsel]]; 
       simpl; reflexivity. 
Defined. 

Theorem correct_sg_CS_option_from_sg_CI : ∀ (S : Type) (P : A_sg_CI S),  
         sg_CS_option_from_sg_CI S (A2C_sg_CI S P) = A2C_sg_CS_option S (A_sg_CS_option_from_sg_CI S P). 
Proof. intros S P. destruct P. 
       unfold A2C_sg_CI, A2C_sg_CS_option, sg_CS_option_from_sg_CI, A_sg_CS_option_from_sg_CI; simpl.  
       rewrite correct_sg_CS_certs_option_from_sg_CI_certs. 
       case (A_sg_CS_proofs_option_from_sg_CI_proofs S (A_eqv_eq S A_sg_CI_eqv) A_sg_CI_bop A_sg_CI_proofs); simpl. 
          intro s. reflexivity. 
          reflexivity. 
Defined. 

Lemma correct_sg_CK_certs_option_from_sg_C_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (sgS : sg_C_proofs S r b), 
       sg_CK_certs_option_from_sg_C_certs S (P2C_sg_C S r b sgS)
       = 
       P2C_sg_CK_option S r b (A_sg_CK_proofs_option_from_sg_C_proofs S r b sgS). 
Proof. intros S r b sgS. destruct sgS. 
       unfold sg_CK_certs_option_from_sg_C_certs, A_sg_CK_proofs_option_from_sg_C_proofs, 
              P2C_sg_C, P2C_sg_CK_option; simpl. 
       destruct A_sg_C_left_cancel_d as [C | NC];
       simpl; reflexivity. 
Defined. 

Theorem correct_sg_CK_from_sg_C : ∀ (S : Type) (P : A_sg_C S),  
        sg_CK_option_from_sg_C S (A2C_sg_C S P) = A2C_sg_CK_option S (A_sg_CK_option_from_sg_C S P). 
Proof. intros S P. destruct P. 
       unfold A2C_sg_C, A2C_sg_CK_option, 
              sg_CK_option_from_sg_C, A_sg_CK_option_from_sg_C; simpl.  
       rewrite correct_sg_CK_certs_option_from_sg_C_certs. 
       case (A_sg_CK_proofs_option_from_sg_C_proofs S (A_eqv_eq S A_sg_C_eqv)
               A_sg_C_bop A_sg_C_proofs); simpl. 
          intro s. reflexivity. 
          reflexivity. 
Defined. 






