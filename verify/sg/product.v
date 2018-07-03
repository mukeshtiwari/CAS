Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.bop.

Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.
Require Import CAS.code.sg_certificates. 
Require Import CAS.code.sg_cert_records. 
Require Import CAS.verify.eqv_proofs_to_certs.
Require Import CAS.verify.sg_proofs_to_certs.

Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.bop.product.  (* for _decide functions *) 
Require Import CAS.verify.eqv.product. 
Require Import CAS.code.cas.sg.product.
Require Import CAS.a_code.a_cas.sg.product.

Section ChecksCorrect.

  Variable S : Type.
  Variable T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable bS : binary_op S.
  Variable bT : binary_op T.
  Variable wS : S.
  Variable f : S -> S.    
  Variable Pf : brel_not_trivial S rS f.
  Variable wT : T.
  Variable g : T -> T.      
  Variable Pg : brel_not_trivial T rT g.  
  Variable symS : brel_symmetric S rS.
  Variable symT : brel_symmetric T rT. 
  Variable transS : brel_transitive S rS.
  Variable transT : brel_transitive T rT. 
  Variable refS : brel_reflexive S rS. 
  Variable refT : brel_reflexive T rT.


Lemma correct_check_commutative_product : 
      ∀ (dS : bop_commutative_decidable S rS bS) (dT : bop_commutative_decidable T rT bT),
        
         check_commutative_product wS wT 
            (p2c_commutative_check S rS bS dS)
            (p2c_commutative_check T rT bT dT)
         = 
         p2c_commutative_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_commutative_decide S T rS rT bS bT wS wT dS dT). 
Proof. intros [cS | [ [s3 s4] ncS] ] [cT | [ [t3 t4] ncT] ]; compute; reflexivity. Defined. 

Lemma correct_check_is_left_product : 
      ∀ (dS : bop_is_left_decidable S rS bS) (dT : bop_is_left_decidable T rT bT),
         
         check_is_left_product wS wT 
            (p2c_is_left_check S rS bS dS)
            (p2c_is_left_check T rT bT dT)
         = 
         p2c_is_left_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_is_left_decide S T rS rT bS bT wS wT dS dT). 
Proof. intros [cS | [ [s3 s4] ncS ] ] [cT | [ [t3 t4] ncT ]]; compute; reflexivity. Defined. 


(*
Lemma correct_assert_not_is_left_product : ∀ (nlS : bop_not_is_left S rS bS), 

    assert_product_not_is_left_left wT 
             (p2c_not_is_left S rS bS nlS)
          = 
          p2c_not_is_left (S * T) 
             (brel_product rS rT)
             (bop_product bS bT)
             (bop_product_not_is_left_left S T rS rT bS bT wT nlS). 
Proof. intros [ [t1 t2] PT ].  compute. reflexivity. Defined. 
*) 

Lemma correct_check_is_right_product : 
      ∀ (dS : bop_is_right_decidable S rS bS) (dT : bop_is_right_decidable T rT bT),
         
         check_is_right_product wS wT
            (p2c_is_right_check S rS bS dS)
            (p2c_is_right_check T rT bT dT)
         = 
         p2c_is_right_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_is_right_decide S T rS rT bS bT wS wT dS dT). 
Proof. intros [cS | [ [s3 s4] ncS]] [cT | [ [t3 t4] ncT]]; compute; reflexivity. Defined. 

(*
Lemma correct_assert_not_is_right_product : 
      ∀ (nrT : bop_not_is_right T rT bT), 
          assert_product_not_is_right_right 
             (p2c_nontrivial S rS ntS)
             (p2c_not_is_right T rT bT nrT)
          = 
          p2c_not_is_right (S * T) 
             (brel_product rS rT)
             (bop_product bS bT)
             (bop_product_not_is_right_right S T rS rT bS bT (brel_get_nontrivial_witness S rS ntS) nrT). 
Proof. intros [ [t1 t2] PT]. compute. reflexivity. Defined. 
*) 

Lemma correct_check_idempotent_product : 
      ∀ (dS : bop_idempotent_decidable S rS bS)  (dT : bop_idempotent_decidable T rT bT),
        
         check_idempotent_product wS wT 
            (p2c_idempotent_check S rS bS dS)
            (p2c_idempotent_check T rT bT dT)
         = 
         p2c_idempotent_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_idempotent_decide S T rS rT bS bT wS wT dS dT). 
Proof. intros [cS | [s3 niS]] [cT | [t3 niT]]; compute; reflexivity. Defined. 


Lemma correct_check_exists_id_product : 
      ∀ (dS : bop_exists_id_decidable S rS bS) (dT : bop_exists_id_decidable T rT bT),
         
         check_exists_id_product 
           (p2c_exists_id_check S rS bS dS)
           (p2c_exists_id_check T rT bT dT)
         =
         p2c_exists_id_check (S * T) 
            (brel_product rS rT)
            (bop_product bS bT)
            (bop_product_exists_id_decide S T rS rT bS bT dS dT).
Proof. intros [[s sP] | nS ] [[t tP] | nT ]; compute; reflexivity. Defined. 


Lemma correct_check_exists_ann_product : 
      ∀ (dS : bop_exists_ann_decidable S rS bS) (dT : bop_exists_ann_decidable T rT bT),
         
         check_exists_ann_product 
           (p2c_exists_ann_check S rS bS dS)
           (p2c_exists_ann_check T rT bT dT)
         =
         p2c_exists_ann_check (S * T) 
            (brel_product rS rT)
            (bop_product bS bT)
            (bop_product_exists_ann_decide S T rS rT bS bT dS dT).
Proof. intros [[s sP] | nS ] [[t tP] | nT ]; compute; reflexivity. Defined. 


Lemma correct_check_selective_product : 
      ∀ (dlS : bop_is_left_decidable S rS bS)
         (dlT : bop_is_left_decidable T rT bT)
         (drS : bop_is_right_decidable S rS bS)
         (drT : bop_is_right_decidable T rT bT),
         p2c_selective_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_selective_decide S T rS rT bS bT wS f Pf symS transS wT g Pg symT transT dlS dlT drS drT)
         = 
         check_selective_product wS wT 
            (p2c_is_left_check S rS bS dlS)
            (p2c_is_left_check T rT bT dlT)
            (p2c_is_right_check S rS bS drS)
            (p2c_is_right_check T rT bT drT). 
Proof. 
       intros [ilS | [ [s3 s4] nilS]] [ilT | [ [t3 t4] nilT]]
              [irS | [ [s5 s6] nirS]] [irT | [ [t5 t6] nirT]]; 
          compute; auto. 
          assert (F := bop_not_left_or_not_right S rS bS wS f Pf symS transS ilS irS). 
             elim F. 
          assert (F := bop_not_left_or_not_right T rT bT wT g Pg symT transT ilT irT). 
             elim F. 
Defined. 


Lemma correct_check_left_cancel_product : 
      ∀ (dS : bop_left_cancellative_decidable S rS bS) (dT : bop_left_cancellative_decidable T rT bT),
         
         p2c_left_cancel_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_left_cancellative_decide S T rS rT bS bT wS refS wT refT dS dT)
         = 
         check_left_cancellative_product  wS wT 
            (p2c_left_cancel_check S rS bS dS)
            (p2c_left_cancel_check T rT bT dT). 
Proof. intros [cS | [ [s3 [s4 s5]] [ncSL ncSR]] ] [cT | [ [t3 [t4 t5]] [ncTL ncTR] ] ]; compute; reflexivity. Defined. 

Lemma correct_check_right_cancel_product : 
      ∀ (dS : bop_right_cancellative_decidable S rS bS) (dT : bop_right_cancellative_decidable T rT bT),
         
         p2c_right_cancel_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_right_cancellative_decide S T rS rT bS bT wS refS wT refT dS dT)
         = 
         check_right_cancellative_product wS wT 
            (p2c_right_cancel_check S rS bS dS)
            (p2c_right_cancel_check T rT bT dT). 
Proof. intros [cS | [ [s3 [s4 s5]] [ncSL ncSR]] ] [cT | [ [t3 [t4 t5]] [ncTL ncTR] ] ]; compute; reflexivity. Defined. 

Lemma correct_check_left_constant_product : 
      ∀ (dS : bop_left_constant_decidable S rS bS) (dT : bop_left_constant_decidable T rT bT),
         
         p2c_left_constant_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_left_constant_decide S T rS rT bS bT wS wT dS dT)
         = 
         check_left_constant_product wS wT 
            (p2c_left_constant_check S rS bS dS)
            (p2c_left_constant_check T rT bT dT).
Proof. intros [cS | [ [s3 [s4 s5]] ncS] ] [cT | [ [t3 [t4 t5]] ncT] ]; compute; reflexivity. Defined. 


Lemma correct_check_right_constant_product : 
      ∀ (dS : bop_right_constant_decidable S rS bS) (dT : bop_right_constant_decidable T rT bT),
         
         p2c_right_constant_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_right_constant_decide S T rS rT bS bT wS wT dS dT)
         = 
         check_right_constant_product wS wT 
            (p2c_right_constant_check S rS bS dS)
            (p2c_right_constant_check T rT bT dT).
Proof. intros [cS | [ [s3 [s4 s5]] ncS] ] [cT | [ [t3 [t4 t5]] ncT] ]; compute; reflexivity. Defined. 


Lemma correct_check_anti_left_product : 
      ∀ (dS : bop_anti_left_decidable S rS bS) (dT : bop_anti_left_decidable T rT bT),
         
         p2c_anti_left_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_anti_left_decide S T rS rT bS bT dS dT)
         = 
         check_anti_left_product 
            (p2c_anti_left_check S rS bS dS)
            (p2c_anti_left_check T rT bT dT).
Proof. intros [cS | [ [s3 s4] ncS] ] [cT | [ [t3 t4] ncT] ]; compute; reflexivity. Defined. 


Lemma correct_check_anti_right_product : 
      ∀ (dS : bop_anti_right_decidable S rS bS)
         (dT : bop_anti_right_decidable T rT bT),
         p2c_anti_right_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_anti_right_decide S T rS rT bS bT dS dT)
         = 
         check_anti_right_product 
            (p2c_anti_right_check S rS bS dS)
            (p2c_anti_right_check T rT bT dT).
Proof. intros [cS | [ [s3 s4] ncS] ] [cT | [ [t3 t4] ncT] ]; compute; reflexivity. Defined.


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


Lemma correct_sg_certs_product : 
      ∀ (pS : sg_proofs S rS bS) (pT : sg_proofs T rT bT),
        
      sg_certs_product wS wT (P2C_sg S rS bS pS) (P2C_sg T rT bT pT) 
      = 
      P2C_sg (S * T) (brel_product rS rT) 
                     (bop_product bS bT) 
                     (sg_proofs_product S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_proofs_product, sg_certs_product, P2C_sg; simpl. 
       rewrite correct_check_idempotent_product.
       rewrite correct_check_selective_product.              
       rewrite correct_check_is_right_product. 
       rewrite correct_check_is_left_product. 
       rewrite correct_check_commutative_product.
       rewrite correct_check_exists_id_product.  
       rewrite correct_check_exists_ann_product. 
       rewrite <- correct_check_anti_left_product. 
       rewrite <- correct_check_anti_right_product.
       rewrite <- correct_check_left_constant_product.       
       rewrite <- correct_check_right_constant_product.        
       rewrite correct_check_left_cancel_product. 
       rewrite correct_check_right_cancel_product. 
       reflexivity. 
Defined. 


Lemma  correct_sg_CK_certs_product : 
      ∀ (pS : sg_CK_proofs S rS bS) (pT : sg_CK_proofs T rT bT),
        
      sg_CK_certs_product (P2C_sg_CK S rS bS pS) (P2C_sg_CK T rT bT pT) 
      = 
      P2C_sg_CK (S * T) 
         (brel_product rS rT) 
         (bop_product bS bT) 
         (sg_CK_proofs_product S T rS rT bS bT eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_CK_proofs_product, sg_CK_certs_product, P2C_sg_CK; simpl. 
       rewrite correct_check_exists_id_product.  
       rewrite correct_check_anti_left_product. 
       rewrite correct_check_anti_right_product. 
       reflexivity. 
Defined.

End ProofsCorrect. 

Theorem correct_sg_product :
      ∀ (S T : Type) (sgS : A_sg S) (sgT : A_sg T), 
         sg_product (A2C_sg S sgS) (A2C_sg T sgT) 
         = 
         A2C_sg (S * T) (A_sg_product S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_product, A2C_sg; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_certs_product. 
       reflexivity. 
Qed. 


Theorem correct_sg_CK_product :
      ∀ (S T : Type) (sgS : A_sg_CK S) (sgT : A_sg_CK T), 
         sg_CK_product (A2C_sg_CK S sgS) (A2C_sg_CK T sgT) 
         = 
         A2C_sg_CK (S * T) (A_sg_CK_product S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CK_product, A2C_sg_CK; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_CK_certs_product. 
       reflexivity. 
Qed. 
