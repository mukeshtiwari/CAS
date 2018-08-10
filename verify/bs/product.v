
Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.bop.

Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.
Require Import CAS.code.bs_certificates. 
Require Import CAS.code.bs_cert_records. 
Require Import CAS.verify.eqv_proofs_to_certs.
Require Import CAS.verify.bs_proofs_to_certs.

Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.bs_properties.
Require Import CAS.theory.bs.product_product.  (* for _decide functions *) 
Require Import CAS.verify.eqv.product. 
Require Import CAS.code.cas.bs.product.
Require Import CAS.a_code.a_cas.bs.product.

Require Import CAS.verify.sg.product.

Section ChecksCorrect.

  Variable S : Type.
  Variable T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable plusS timesS : binary_op S.
  Variable plusT timesT : binary_op T.
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


Lemma bop_product_left_distributive_check_correct : 
  ∀ (pS_d : bop_left_distributive_decidable S rS plusS timesS) 
     (pT_d : bop_left_distributive_decidable T rT plusT timesT), 
     bop_product_left_distributive_check wS wT  
       (p2c_left_distributive S rS plusS timesS pS_d)
       (p2c_left_distributive T rT plusT timesT pT_d)
     = 
     @p2c_left_distributive (S * T) 
        (brel_product rS rT)
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (bop_product_left_distributive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. intros [ ldS | [ [s1 [s2 s3]] nldS]] [ ldT | [ [t1 [t2 t3]] nldT]]; compute; reflexivity. Qed. 

Lemma bop_product_right_distributive_check_correct : 
  ∀ (pS_d : bop_right_distributive_decidable S rS plusS timesS) 
     (pT_d : bop_right_distributive_decidable T rT plusT timesT), 
   bop_product_right_distributive_check wS wT 
       (p2c_right_distributive S rS plusS timesS pS_d)
       (p2c_right_distributive T rT plusT timesT pT_d)
     = 
     p2c_right_distributive (S * T) 
        (brel_product rS rT)
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (bop_product_right_distributive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. intros 
       [ ldS | [ [s1 [s2 s3]] nldS]] 
       [ ldT | [ [t1 [t2 t3]] nldT]]; compute; reflexivity. 
Qed. 


Lemma bop_product_plus_id_is_times_ann_check_correct : 
  ∀ (pS_d : bops_id_equals_ann_decidable S rS plusS timesS)
     (pT_d : bops_id_equals_ann_decidable T rT plusT timesT), 
   p2c_plus_id_equals_times_ann (S * T) 
      (brel_product rS rT)
      (bop_product plusS plusT)
      (bop_product timesS timesT)
      (bop_product_id_equals_ann_decide S T rS rT plusS timesS plusT timesT pS_d pT_d)
   = 
   bop_product_plus_id_is_times_ann_check 
      (p2c_plus_id_equals_times_ann S rS plusS timesS pS_d)
      (p2c_plus_id_equals_times_ann T rT plusT timesT pT_d). 
Proof. intros [ eqS | neqS] [eqT | neqT] ; compute; reflexivity. Qed. 


Lemma bop_product_times_id_equals_plus_ann_check_correct : 
  ∀ (pS_d : bops_id_equals_ann_decidable S rS timesS plusS)
     (pT_d : bops_id_equals_ann_decidable T rT timesT plusT), 
   p2c_times_id_equals_plus_ann (S * T) 
      (brel_product rS rT)
      (bop_product plusS plusT)
      (bop_product timesS timesT)
      (bop_product_id_equals_ann_decide S T rS rT timesS plusS timesT plusT pS_d pT_d)
   = 
   bop_product_times_id_equals_plus_ann_check 
      (p2c_times_id_equals_plus_ann S rS plusS timesS pS_d) 
      (p2c_times_id_equals_plus_ann T rT plusT timesT pT_d). 
Proof. intros [ eqS | neqS] [eqT | neqT] ; compute; reflexivity. Qed. 

Lemma bop_product_left_left_absorbtive_check_correct : 
  ∀ (pS_d : bops_left_left_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_left_left_absorptive_decidable T rT plusT timesT), 
   bop_product_left_left_absorptive_check wS wT 
       (p2c_left_left_absorptive S rS plusS timesS pS_d)
       (p2c_left_left_absorptive T rT plusT timesT pT_d)
     = 
     p2c_left_left_absorptive (S * T) 
        (brel_product rS rT)
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (bops_product_left_left_absorptive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. intros [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. Qed. 

Lemma bop_product_left_right_absorbtive_check_correct : 
  ∀ (pS_d : bops_left_right_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_left_right_absorptive_decidable T rT plusT timesT), 
   bop_product_left_right_absorptive_check wS wT 
       (p2c_left_right_absorptive S rS plusS timesS pS_d)
       (p2c_left_right_absorptive T rT plusT timesT pT_d)
     = 
     p2c_left_right_absorptive (S * T) 
        (brel_product rS rT)
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (bops_product_left_right_absorptive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. intros [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. Qed. 

Lemma bop_product_right_left_absorbtive_check_correct : 
  ∀ (pS_d : bops_right_left_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_right_left_absorptive_decidable T rT plusT timesT), 
   bop_product_right_left_absorptive_check wS wT 
       (p2c_right_left_absorptive S rS plusS timesS pS_d)
       (p2c_right_left_absorptive T rT plusT timesT pT_d)
     = 
     p2c_right_left_absorptive (S * T) 
        (brel_product rS rT)
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (bops_product_right_left_absorptive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. intros [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. Qed. 

Lemma bop_product_right_right_absorbtive_check_correct : 
  ∀ (pS_d : bops_right_right_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_right_right_absorptive_decidable T rT plusT timesT), 
   bop_product_right_right_absorptive_check wS wT
       (p2c_right_right_absorptive S rS plusS timesS pS_d)
       (p2c_right_right_absorptive T rT plusT timesT pT_d)
     = 
     p2c_right_right_absorptive (S * T) 
        (brel_product rS rT)
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (bops_product_right_right_absorptive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. intros [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. Qed. 


Lemma  correct_bs_certs_product : 
  ∀ (eqvS : eqv_proofs S rS)
     (eqvT : eqv_proofs T rT)
     (bsS : bs_proofs S rS plusS timesS)
     (bsT : bs_proofs T rT plusT timesT), 
    bs_certs_product wS wT (P2C_bs S rS plusS timesS bsS) (P2C_bs T rT plusT timesT bsT)
    =
    P2C_bs (S * T) (brel_product rS rT) (bop_product plusS plusT) (bop_product timesS timesT) 
       (bs_proofs_product S T rS rT plusS timesS plusT timesT wS wT eqvS eqvT bsS bsT). 
Proof. intros eqvS eqvT bsS bsT. 
       unfold bs_certs_product, bs_proofs_product, P2C_bs; simpl. 
       rewrite bop_product_left_distributive_check_correct. 
       rewrite bop_product_right_distributive_check_correct. 
       rewrite bop_product_plus_id_is_times_ann_check_correct. 
       rewrite bop_product_times_id_equals_plus_ann_check_correct.
       rewrite bop_product_left_left_absorbtive_check_correct. 
       rewrite bop_product_left_right_absorbtive_check_correct. 
       rewrite bop_product_right_left_absorbtive_check_correct. 
       rewrite bop_product_right_right_absorbtive_check_correct. 
       reflexivity. 
Defined.

Lemma  correct_semiring_certs_product : 
  ∀ (eqvS : eqv_proofs S rS)
     (eqvT : eqv_proofs T rT)
     (bsS : semiring_proofs S rS plusS timesS)
     (bsT : semiring_proofs T rT plusT timesT), 
    semiring_certs_product wS wT (P2C_semiring S rS plusS timesS bsS) (P2C_semiring T rT plusT timesT bsT)
    =
    P2C_semiring (S * T) (brel_product rS rT) (bop_product plusS plusT) (bop_product timesS timesT) 
       (semiring_proofs_product S T rS rT plusS timesS plusT timesT wS wT eqvS eqvT bsS bsT). 
Proof. intros eqvS eqvT bsS bsT. 
       unfold semiring_certs_product, semiring_proofs_product, P2C_semiring; simpl. 
       rewrite bop_product_plus_id_is_times_ann_check_correct. 
       rewrite bop_product_times_id_equals_plus_ann_check_correct.
       rewrite bop_product_left_left_absorbtive_check_correct. 
       rewrite bop_product_left_right_absorbtive_check_correct. 
       reflexivity. 
Defined. 



End ChecksCorrect.

Theorem correct_bs_product : ∀ (S T : Type) (bsS: A_bs S) (bsT : A_bs T), 
   bs_product (A2C_bs S bsS) (A2C_bs T bsT)
   =
   A2C_bs (S * T) (A_bs_product S T bsS bsT). 
Proof. intros S T bsS bsT. 
       unfold bs_product, A_bs_product, A2C_bs; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_certs_product. 
       rewrite <- correct_sg_certs_product. 
       rewrite <- correct_bs_certs_product. 
       reflexivity. 
Qed. 


Theorem correct_semiring_product : ∀ (S T : Type) (bsS: A_semiring S) (bsT : A_semiring T), 
   semiring_product (A2C_semiring S bsS) (A2C_semiring T bsT)
   =
   A2C_semiring (S * T) (A_semiring_product S T bsS bsT). 
Proof. intros S T bsS bsT. 
       unfold semiring_product, A_semiring_product, A2C_semiring; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_certs_product. 
       rewrite <- correct_sg_C_certs_product. 
       rewrite <- correct_semiring_certs_product. 
       reflexivity. 
Qed. 


Theorem correct_dioid_product : ∀ (S T : Type) (bsS: A_dioid S) (bsT : A_dioid T), 
   dioid_product S T (A2C_dioid S bsS) (A2C_dioid T bsT)
   =
   A2C_dioid (S * T) (A_dioid_product S T bsS bsT). 
Proof. intros S T bsS bsT. 
       unfold dioid_product, A_dioid_product, A2C_dioid; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_certs_product. 
       rewrite <- correct_sg_CI_certs_product. 
       rewrite <- correct_semiring_certs_product. 
       reflexivity. 
Qed. 

Check A_lattice_product.

Check A_distributive_lattice_product. 