Require Import CAS.code.basic_types. 
Require Import CAS.code.cef. 
Require Import CAS.code.certificates.
Require Import CAS.code.cert_records.
Require Import CAS.code.cas_records.
Require Import CAS.code.cast.
Require Import CAS.theory.facts. 
Require Import CAS.theory.properties.        (* ~~ certificates *) 
Require Import CAS.a_code.proof_records.     (* ~~ cert_records *) 
Require Import CAS.a_code.a_cas_records.     
Require Import CAS.a_code.a_cast.
Require Import CAS.verify.proofs_to_certs. 

(* upcasts *) 

Lemma correct_sg_certs_from_sg_C_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (eqvS : eqv_proofs S r) (sgS : sg_C_proofs S r b), 
       sg_certs_from_sg_C_certs S r b 
          (P2C_eqv S r eqvS)
          (P2C_sg_C S r b sgS)
       = 
       P2C_sg S r b (A_sg_proofs_from_sg_C_proofs S r b eqvS sgS). 
Proof. intros S r b eqvS sgS. destruct sgS. destruct eqvS. 
       destruct A_eqv_nontrivial as [ [s Ps] [f Pf] ]. 
       unfold sg_certs_from_sg_C_certs, A_sg_proofs_from_sg_C_proofs, P2C_sg, P2C_sg_C; simpl. 
       reflexivity.        
Defined. 

Theorem correct_sg_from_sg_C : ∀ (S : Type) (P : A_sg_C S),  
         sg_from_sg_C S (A2C_sg_C S P) = A2C_sg S (A_sg_from_sg_C S P). 
Proof. intros S P. destruct P. destruct A_sg_C_eqv.
        unfold sg_from_sg_C, A_sg_from_sg_C, A2C_sg_C, A2C_sg; simpl. 
       rewrite correct_sg_certs_from_sg_C_certs. reflexivity. 
Defined. 


Lemma correct_sg_C_certs_from_sg_CI_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (eqvS : eqv_proofs S r) (sgS : sg_CI_proofs S r b), 
       sg_C_certs_from_sg_CI_certs S r b (P2C_eqv S r eqvS) (P2C_sg_CI S r b sgS)
       = 
       P2C_sg_C S r b (A_sg_C_proofs_from_sg_CI_proofs S r b eqvS sgS). 
Proof. intros S r b eqvS sgS. destruct sgS. destruct eqvS. 
       destruct A_eqv_nontrivial as [ [s Ps] [f Pf] ]. 
       unfold sg_C_certs_from_sg_CI_certs, A_sg_C_proofs_from_sg_CI_proofs, P2C_sg_C, P2C_sg_CI; 
       simpl. 
       destruct A_sg_CI_selective_d as [ selS | [ [s1 s2] [P1 P2] ] ]; simpl. 
       reflexivity.        
       reflexivity.        
Defined. 

Theorem correct_sg_C_from_sg_CI : ∀ (S : Type) (P : A_sg_CI S),  
         sg_C_from_sg_CI S (A2C_sg_CI S P) = A2C_sg_C S (A_sg_C_from_sg_CI S P). 
Proof. intros S P. unfold sg_C_from_sg_CI, A_sg_C_from_sg_CI, A2C_sg_CI, A2C_sg_C; simpl. 
       rewrite correct_sg_C_certs_from_sg_CI_certs. reflexivity. 
Defined. 

Lemma correct_sg_CI_certs_from_sg_CS_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (sgS : sg_CS_proofs S r b), 
       sg_CI_certs_from_sg_CS_certs S (P2C_sg_CS S r b sgS)
       = 
       P2C_sg_CI S r b (A_sg_CI_proofs_from_sg_CS_proofs S r b sgS). 
Proof. intros S r b sgS. destruct sgS. 
       unfold sg_CI_certs_from_sg_CS_certs, 
              A_sg_CI_proofs_from_sg_CS_proofs, P2C_sg_CI, P2C_sg_CS; simpl. 
       reflexivity.        
Defined. 


Theorem correct_sg_CI_from_sg_CS : ∀ (S : Type) (P : A_sg_CS S),  
         sg_CI_from_sg_CS S (A2C_sg_CS S P) = A2C_sg_CI S (A_sg_CI_from_sg_CS S P). 
Proof. intros S P. unfold sg_CI_from_sg_CS, A_sg_CI_from_sg_CS, A2C_sg_CI, A2C_sg_CS; simpl. 
       rewrite correct_sg_CI_certs_from_sg_CS_certs. reflexivity. 
Defined. 


Lemma correct_sg_C_certs_from_sg_CK_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (eqvS : eqv_proofs S r) (sgS : sg_CK_proofs S r b), 
       sg_C_certs_from_sg_CK_certs S r b (P2C_eqv S r eqvS) (P2C_sg_CK S r b sgS)
       = 
       P2C_sg_C S r b (A_sg_C_proofs_from_sg_CK_proofs S r b eqvS sgS). 
Proof. intros S r b eqvS sgS. destruct sgS. destruct eqvS. 
       destruct A_eqv_nontrivial as [ [s Ps] [f Pf] ]. 
       destruct A_sg_CK_exists_id_d as [ [i Pi] | no_id ]; 
       unfold sg_C_certs_from_sg_CK_certs, A_sg_C_proofs_from_sg_CK_proofs, P2C_sg_C, P2C_sg_CK; 
       simpl. 
          reflexivity.        
          compute. reflexivity.        
Defined. 

Theorem correct_sg_C_from_sg_CK : ∀ (S : Type) (P : A_sg_CK S),  
         sg_C_from_sg_CK S (A2C_sg_CK S P) = A2C_sg_C S (A_sg_C_from_sg_CK S P). 
Proof. intros S P. unfold sg_C_from_sg_CK, A_sg_C_from_sg_CK, A2C_sg_CK, A2C_sg_C; simpl. 
       rewrite correct_sg_C_certs_from_sg_CK_certs. reflexivity. 
Defined. 


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






