Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.bop.

Require Import CAS.code.sg_certificates. 
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.cas.sg.left_sum.

Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cas.sg.left_sum.

Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.bop.left_sum.  (* for _decide functions *) 

Require Import CAS.verify.eqv.sum. 
Require Import CAS.verify.eqv_proofs_to_certs.
Require Import CAS.verify.sg_proofs_to_certs.


Section ChecksCorrect.

  Variable S : Type.
  Variable T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable wS : S.
  Variable wT : T.
  Variable bS : binary_op S.
  Variable bT : binary_op T.
  Variable symS : brel_symmetric S rS.
  Variable symT : brel_symmetric T rT. 
  Variable transS : brel_transitive S rS.
  Variable transT : brel_transitive T rT. 
  Variable refS : brel_reflexive S rS. 
  Variable refT : brel_reflexive T rT.


Lemma correct_check_commutative_left_sum :  ∀ (dS : bop_commutative_decidable S rS bS) (dT : bop_commutative_decidable T rT bT),
         
         check_commutative_left_sum 
            (p2c_commutative_check S rS bS dS)
            (p2c_commutative_check T rT bT dT)
         = 
         p2c_commutative_check (S + T) 
            (brel_sum rS rT) 
            (bop_left_sum bS bT)
            (bop_left_sum_commutative_decide S T rS rT bS bT refS dS dT). 
Proof. intros [cS | [ [s3 s4] ncS]] [cT | [ [t3 t4] ncT]]; compute; reflexivity. Defined. 


Lemma correct_check_idempotent_left_sum : ∀ (dS : bop_idempotent_decidable S rS bS) (dT : bop_idempotent_decidable T rT bT),
         
         check_idempotent_left_sum 
            (p2c_idempotent_check S rS bS dS)
            (p2c_idempotent_check T rT bT dT)
         = 
         p2c_idempotent_check (S + T) 
            (brel_sum rS rT) 
            (bop_left_sum bS bT)
            (bop_left_sum_idempotent_decide S T rS rT bS bT dS dT). 
Proof. intros [cS | [s4 ncS]] [cT | [t4 ncT]]; compute; reflexivity. Defined. 

Lemma correct_check_selective_left_sum : ∀ (dS : bop_selective_decidable S rS bS) (dT : bop_selective_decidable T rT bT),
         
         check_selective_left_sum 
            (p2c_selective_check S rS bS dS)
            (p2c_selective_check T rT bT dT)
         = 
         p2c_selective_check (S + T) 
            (brel_sum rS rT) 
            (bop_left_sum bS bT)
            (bop_left_sum_selective_decide S T rS rT bS bT refS dS dT). 
Proof. intros [cS | [ [s3 s4] ncS]] [cT | [ [t3 t4] ncT]]; compute; reflexivity. Defined. 

Lemma correct_check_exists_id_left_sum : ∀ (dT : bop_exists_id_decidable T rT bT),
    
         check_exists_id_left_sum (p2c_exists_id_check T rT bT dT)
         =
         p2c_exists_id_check (S + T) 
            (brel_sum rS rT)
            (bop_left_sum bS bT)
            (bop_left_sum_exists_id_decide S T rS rT bS bT refS wT dT).
Proof. intros [[t tP] | nT ]; compute; reflexivity. Defined. 

Lemma correct_check_exists_ann_left_sum : ∀ (dS : bop_exists_ann_decidable S rS bS), 
         check_exists_ann_left_sum (p2c_exists_ann_check S rS bS dS)
         =
         p2c_exists_ann_check (S + T) 
            (brel_sum rS rT)
            (bop_left_sum bS bT)
            (bop_left_sum_exists_ann_decide S T rS rT bS bT wS refS dS).
Proof. intros [[s sP] | nS ]; compute; reflexivity. Defined. 


End ChecksCorrect. 

Section ProofsCorrect.

  Variable S : Type.
  Variable T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable wS : S.
  Variable f : S -> S.    
  Variable Pf : brel_not_trivial S rS f.
  Variable wT : T.
  Variable g : T -> T.      
  Variable Pg : brel_not_trivial T rT g.  
  Variable bS : binary_op S.
  Variable bT : binary_op T.
  Variable eS : eqv_proofs S rS.
  Variable eT : eqv_proofs T rT. 


Lemma correct_sg_certs_left_sum : ∀ (pS : sg_proofs S rS bS) (pT : sg_proofs T rT bT),

      sg_certs_left_sum wS f wT g (P2C_sg S rS bS pS) (P2C_sg T rT bT pT) 
      = 
      P2C_sg (S + T) (brel_sum rS rT) 
                     (bop_left_sum bS bT) 
                     (sg_proofs_left_sum S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_proofs_left_sum, sg_certs_left_sum, P2C_sg; simpl. 
       rewrite <- correct_check_commutative_left_sum. 
       rewrite <- correct_check_selective_left_sum. 
       rewrite correct_check_idempotent_left_sum. 
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum.
       reflexivity.        
Defined. 

Lemma correct_sg_C_certs_left_sum : ∀ (pS : sg_C_proofs S rS bS) (pT : sg_C_proofs T rT bT),
        
      sg_C_certs_left_sum wS f wT g (P2C_sg_C S rS bS pS) (P2C_sg_C T rT bT pT) 
      = 
      P2C_sg_C (S + T) (brel_sum rS rT) 
                     (bop_left_sum bS bT) 
                     (sg_C_proofs_left_sum S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_C_proofs_left_sum, sg_C_certs_left_sum, P2C_sg_C; simpl. 
       rewrite <- correct_check_selective_left_sum. 
       rewrite correct_check_idempotent_left_sum. 
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum. 
       reflexivity. 
Defined. 

Lemma correct_sg_CS_certs_left_sum : ∀ (pS : sg_CS_proofs S rS bS) (pT : sg_CS_proofs T rT bT),
        
      sg_CS_certs_left_sum (P2C_sg_CS S rS bS pS) (P2C_sg_CS T rT bT pT) 
      = 
      P2C_sg_CS (S + T) (brel_sum rS rT) 
                     (bop_left_sum bS bT) 
                     (sg_CS_proofs_left_sum S T rS rT bS bT wS wT eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_CS_proofs_left_sum, sg_CS_certs_left_sum, P2C_sg_CS; simpl. 
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum. 
       reflexivity. 
Defined. 

Lemma correct_sg_CI_certs_left_sum : ∀ (pS : sg_CI_proofs S rS bS) (pT : sg_CI_proofs T rT bT),
      sg_CI_certs_left_sum (P2C_sg_CI S rS bS pS) (P2C_sg_CI T rT bT pT) 
      = 
      P2C_sg_CI (S + T) (brel_sum rS rT) 
                     (bop_left_sum bS bT) 
                     (sg_CI_proofs_left_sum S T rS rT bS bT wS wT eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_CI_proofs_left_sum, sg_CI_certs_left_sum, P2C_sg_CI; simpl. 
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum. 
       rewrite <- correct_check_selective_left_sum. 
       reflexivity. 
Defined.

End ProofsCorrect. 


Theorem correct_sg_left_sum : ∀ (S T : Type) (sgS : A_sg S) (sgT : A_sg T), 
      
         sg_left_sum (A2C_sg S sgS) (A2C_sg T sgT) 
         = 
         A2C_sg (S + T) (A_sg_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_left_sum, A2C_sg. simpl. 
       rewrite correct_eqv_sum. 
       rewrite <- correct_sg_certs_left_sum. 
       reflexivity. 
Qed. 

Theorem correct_sg_C_left_sum : ∀ (S T : Type) (sgS : A_sg_C S) (sgT : A_sg_C T), 
      
         sg_C_left_sum (A2C_sg_C S sgS) (A2C_sg_C T sgT) 
         = 
         A2C_sg_C (S + T) (A_sg_C_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_C_left_sum, A2C_sg_C. simpl. 
       rewrite correct_eqv_sum. 
       rewrite <- correct_sg_C_certs_left_sum. 
       reflexivity. 
Qed. 

Theorem correct_sg_CS_left_sum : ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_CS T), 
      
         sg_CS_left_sum (A2C_sg_CS S sgS) (A2C_sg_CS T sgT) 
         = 
         A2C_sg_CS (S + T) (A_sg_CS_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CS_left_sum, A2C_sg_CS. simpl. 
       rewrite correct_eqv_sum. 
       rewrite <- correct_sg_CS_certs_left_sum. 
       reflexivity. 
Qed. 


Theorem correct_sg_CI_left_sum : ∀ (S T : Type) (sgS : A_sg_CI S) (sgT : A_sg_CI T), 
      
         sg_CI_left_sum (A2C_sg_CI S sgS) (A2C_sg_CI T sgT) 
         = 
         A2C_sg_CI (S + T) (A_sg_CI_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CI_left_sum, A2C_sg_CI. simpl. 
       rewrite correct_eqv_sum. 
       rewrite <- correct_sg_CI_certs_left_sum. 
       reflexivity. 
Qed. 
