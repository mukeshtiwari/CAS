Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.combined.

Require Import CAS.code.sg_certificates. 
Require Import CAS.code.sg_cert_records. 
Require Import CAS.code.cas.sg.llex.

Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cas.sg.llex.

Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.bop.llex.  (* for _decide functions *) 

Require Import CAS.verify.eqv.product. 
Require Import CAS.verify.eqv_proofs_to_certs.
Require Import CAS.verify.sg_proofs_to_certs.

Section ChecksCorrect.

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
  Variable symS : brel_symmetric S rS.
  Variable symT : brel_symmetric T rT. 
  Variable transS : brel_transitive S rS.
  Variable transT : brel_transitive T rT. 
  Variable refS : brel_reflexive S rS. 
  Variable refT : brel_reflexive T rT.
  Variable congS : brel_congruence S rS rS.
  
  Variable commS : bop_commutative S rS bS.
  Variable selS : bop_selective S rS bS.
  Variable b_congS : bop_congruence S rS bS.  

  Lemma correct_check_commutative_llex : ∀ (dT : bop_commutative_decidable T rT bT),
      
         p2c_commutative_check (S * T) 
            (brel_product rS rT) 
            (bop_llex rS bS bT)
            (bop_llex_commutative_decide S T rS rT bS bT wS congS refS symS transS refT selS commS dT)
         = 
         check_commutative_llex wS (p2c_commutative_check T rT bT dT). 
Proof. intros [cT | [ [t3 t4] ncT]]; compute; reflexivity. Defined. 


Lemma correct_check_idempotent_llex : ∀ (dT : bop_idempotent_decidable T rT bT),

       p2c_idempotent_check (S * T) 
            (brel_product rS rT) 
            (bop_llex rS bS bT) 
            (bop_llex_idempotent_decide S T rS rT bS bT wS refS selS dT)
         = 
         check_idempotent_llex wS (p2c_idempotent_check T rT bT dT).
Proof. intros [cT | [t3 niT]]; compute; reflexivity. Defined. 

Lemma correct_check_exists_id_llex : 
      ∀ (dS : bop_exists_id_decidable S rS bS) (dT : bop_exists_id_decidable T rT bT),
         
         p2c_exists_id_check (S * T) 
            (brel_product rS rT)
            (bop_llex rS bS bT)
            (bop_llex_exists_id_decide S T rS rT bS bT refS symS transS refT commS dS dT)
         =
         check_exists_id_llex 
           (p2c_exists_id_check S rS bS dS)
           (p2c_exists_id_check T rT bT dT). 
Proof. intros [[s sP] | nS ] [[t tP] | nT ]; compute; reflexivity. Defined. 

Lemma correct_check_exists_ann_llex : ∀ (dS : bop_exists_ann_decidable S rS bS) (dT : bop_exists_ann_decidable T rT bT),

         p2c_exists_ann_check (S * T) 
            (brel_product rS rT)
            (bop_llex rS bS bT)
            (bop_llex_exists_ann_decide S T rS rT bS bT refS symS transS refT commS dS dT)
         =
         check_exists_ann_llex 
           (p2c_exists_ann_check S rS bS dS)
           (p2c_exists_ann_check T rT bT dT). 
Proof. intros [[s sP] | nS ] [[t tP] | nT ]; compute; reflexivity. Defined. 

Lemma correct_check_selective_llex : ∀ (dT : bop_selective_decidable T rT bT),

         p2c_selective_check (S * T) 
            (brel_product rS rT) 
            (bop_llex rS bS bT)
            (bop_llex_selective_decide S T rS rT bS bT wS
              refS symS transS refT b_congS commS selS dT)
         = 
         check_selective_llex wS (p2c_selective_check T rT bT dT). 
Proof.  intros [selT | [ [t1 t2] P]]; compute; reflexivity. Defined. 

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


Lemma correct_sg_CI_certs_llex : ∀ (pS : sg_CS_proofs S rS bS) (pT : sg_CI_proofs T rT bT),
      sg_CI_certs_llex rS bS wS  
                           (P2C_sg_CS S rS bS pS) 
                           (P2C_sg_CI T rT bT pT) 
      = 
      P2C_sg_CI (S * T) (brel_product rS rT) 
                     (bop_llex rS bS bT) 
                     (sg_CI_proofs_llex S T rS rT bS bT wS eS eT pS pT).
Proof. intros pS pT. 
       unfold sg_CI_proofs_llex, sg_CI_certs_llex, P2C_sg_CI, P2C_sg_CS; simpl. 
       rewrite correct_check_exists_id_llex.  
       rewrite correct_check_exists_ann_llex. 
       rewrite correct_check_selective_llex. 
       reflexivity. 
Defined. 

Lemma correct_sg_CS_certs_llex : ∀ (pS : sg_CS_proofs S rS bS) (pT : sg_CS_proofs T rT bT),
      sg_CS_certs_llex rS bS (P2C_sg_CS S rS bS pS) (P2C_sg_CS T rT bT pT) 
      = 
      P2C_sg_CS (S * T) (brel_product rS rT) 
                     (bop_llex rS bS bT) 
                     (sg_CS_proofs_llex S T rS rT bS bT eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_CS_proofs_llex, sg_CS_certs_llex, P2C_sg_CS; simpl. 
       rewrite correct_check_exists_id_llex.  
       rewrite correct_check_exists_ann_llex. 
       reflexivity. 
Defined. 


Lemma correct_sg_C_certs_llex :  ∀(pS : sg_CS_proofs S rS bS)  (pT : sg_C_proofs T rT bT),
        
      sg_C_certs_llex rS bS wS f wT g (P2C_sg_CS S rS bS pS) (P2C_sg_C T rT bT pT) 
      = 
      P2C_sg_C (S * T) (brel_product rS rT) 
                       (bop_llex rS bS bT) 
                       (sg_C_proofs_llex S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_C_proofs_llex, sg_C_certs_llex, P2C_sg_C, P2C_sg_CS; simpl. 
       rewrite correct_check_exists_id_llex.  
       rewrite correct_check_exists_ann_llex. 
       rewrite correct_check_selective_llex.
       rewrite correct_check_idempotent_llex.        
       reflexivity. 
Defined. 

  
Lemma correct_sg_certs_llex : ∀ (pS : sg_CS_proofs S rS bS) (pT : sg_proofs T rT bT),

      sg_certs_llex rS bS wS f wT g (P2C_sg_CS S rS bS pS) (P2C_sg T rT bT pT) 
      = 
      P2C_sg (S * T) (brel_product rS rT) 
                     (bop_llex rS bS bT) 
                     (sg_proofs_llex S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT.
       unfold sg_certs_llex, sg_proofs_llex, P2C_sg; simpl. 
       rewrite correct_check_exists_id_llex.  
       rewrite correct_check_exists_ann_llex. 
       rewrite correct_check_selective_llex.
       rewrite correct_check_idempotent_llex.                      
       rewrite correct_check_commutative_llex.
       reflexivity. 
Defined. 

End ProofsCorrect.   


Theorem correct_sg_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg T), 
         sg_llex (A2C_sg_CS S sgS) (A2C_sg T sgT) 
         = 
         A2C_sg (S * T) (A_sg_llex S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_llex, A2C_sg, A2C_sg_CS; simpl. 
       rewrite <- correct_sg_certs_llex. 
       rewrite correct_eqv_product. 
       reflexivity. 
Qed. 


Theorem correct_sg_C_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_C T), 
         sg_C_llex (A2C_sg_CS S sgS) (A2C_sg_C T sgT) 
         = 
         A2C_sg_C (S * T) (A_sg_C_llex S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_C_llex, A2C_sg_C, A2C_sg_CS; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_C_certs_llex. 
       reflexivity. 
Qed. 

Theorem correct_sg_CS_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_CS T), 
         sg_CS_llex (A2C_sg_CS S sgS) (A2C_sg_CS T sgT) 
         = 
         A2C_sg_CS (S * T) (A_sg_CS_llex S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CS_llex, A2C_sg_CS; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_CS_certs_llex. 
       reflexivity. 
Qed. 

Theorem correct_sg_CI_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_CI T), 
         sg_CI_llex (A2C_sg_CS S sgS) (A2C_sg_CI T sgT) 
         = 
         A2C_sg_CI (S * T) (A_sg_CI_llex S T sgS sgT). 
Proof. intros S T sgS sgT. destruct sgS; destruct sgT. 
       unfold sg_CI_llex, A2C_sg_CI, A2C_sg_CS; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_CI_certs_llex. 
       reflexivity. 
Qed. 
