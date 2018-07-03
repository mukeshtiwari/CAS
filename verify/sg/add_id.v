Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.bop.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties. 
Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.
Require Import CAS.code.sg_certificates. 
Require Import CAS.code.sg_cert_records. 
Require Import CAS.verify.eqv_proofs_to_certs.
Require Import CAS.verify.sg_proofs_to_certs.

Require Import CAS.theory.bop.add_id. 
Require Import CAS.verify.eqv.add_constant. 
Require Import CAS.code.cas.sg.add_id.
Require Import CAS.a_code.a_cas.sg.add_id. 

Section CertsCorrect.

  Variable S : Type.
  Variable r : brel S.
  Variable b : binary_op S.
  Variable c : cas_constant. 
  Variable Q : eqv_proofs S r. 

  Lemma bop_add_id_commutative_check_correct :  ∀ (p_d : bop_commutative_decidable S r b)     
     (refS : brel_reflexive S r),  
     p2c_commutative_check (with_constant S)
                         (brel_add_constant r c) 
                         (bop_add_id b c)
                         (bop_add_id_commutative_decide S r c b refS p_d)
     =                          
     bop_add_id_commutative_check (p2c_commutative_check S r b p_d). 
Proof. intros [p | [ [s1 s2] np]] refS; compute; reflexivity. Qed. 


Lemma bop_add_id_selective_check_correct : ∀ (p_d : bop_selective_decidable S r b)
     (refS : brel_reflexive S r) , 
     p2c_selective_check (with_constant S)
                         (brel_add_constant r c) 
                         (bop_add_id b c)
                         (bop_add_id_selective_decide S r c b refS p_d)
     =                          
     bop_add_id_selective_check (p2c_selective_check S r b p_d). 
Proof. intros [p | [ [s1 s2] np]] refS; compute; reflexivity. Qed. 

Lemma bop_add_id_idempotent_check_correct : ∀ p_d : bop_idempotent_decidable S r b, 
     p2c_idempotent_check (with_constant S)
                         (brel_add_constant r c) 
                         (bop_add_id b c)
                         (bop_add_id_idempotent_decide S r c b p_d)
     =                          
     bop_add_id_idempotent_check (p2c_idempotent_check S r b p_d). 
Proof. intros [p | [s np] ]; compute; reflexivity. Qed. 


Lemma bop_add_id_left_cancellative_check_correct :       
     ∀ (symS : brel_symmetric S r) (q_d : bop_anti_left_decidable S r b) (p_d : bop_left_cancellative_decidable S r b), 

     p2c_left_cancel_check (with_constant S)
                           (brel_add_constant r c)
                           (bop_add_id b c)
                           (bop_add_id_left_cancellative_decide S r c b symS q_d p_d)
     =                          
     bop_add_id_left_cancellative_check c (p2c_anti_left_check S r b q_d) 
                                          (p2c_left_cancel_check S r b p_d). 
Proof. intros symS  [ q | [[s1 s2] nq] ] [p | [ [s3 [s4 s5]] np] ]; compute; reflexivity. Qed. 


Lemma bop_add_id_right_cancellative_check_correct : 
      ∀ (symS : brel_symmetric S r) (q_d : bop_anti_right_decidable S r b) (p_d : bop_right_cancellative_decidable S r b), 

     p2c_right_cancel_check (with_constant S)
                            (brel_add_constant r c)
                            (bop_add_id b c)
                            (bop_add_id_right_cancellative_decide S r c b symS q_d p_d)
     =                          
     bop_add_id_right_cancellative_check c (p2c_anti_right_check S r b q_d)
                                           (p2c_right_cancel_check S r b p_d). 
Proof. intros symS  [ q | [[s1 s2] nq] ] [p | [ [s3 [s4 s5]] np] ]; compute; reflexivity. Qed. 

Lemma bop_add_id_exists_ann_check_correct : ∀ (s : S) (refS : brel_reflexive S r) (p_d : bop_exists_ann_decidable S r b), 
     p2c_exists_ann_check (with_constant S)
                          (brel_add_constant r c)
                          (bop_add_id b c)
        (bop_add_id_exists_ann_decide S r c b s refS p_d)
     =                          
     bop_add_id_exists_ann_check (p2c_exists_ann_check S r b p_d). 
Proof. intros s refS [ [a p] | np ]; compute; reflexivity. Qed. 

Lemma correct_sg_certs_add_id : ∀ (s : S) (f : S -> S) (Pf : brel_not_trivial S r f) (P : sg_proofs S r b), 
       sg_certs_add_id c s f (P2C_sg S r b P) 
       = 
       P2C_sg (with_constant S) 
              (brel_add_constant r c) 
              (bop_add_id b c) 
              (sg_proofs_add_id S r c b s f Pf Q P). 
Proof. intros s f Pf P. 
       destruct P. destruct Q. 
       unfold sg_proofs_add_id, P2C_sg, sg_certs_add_id; simpl. 
       rewrite bop_add_id_commutative_check_correct. 
       rewrite bop_add_id_selective_check_correct. 
       rewrite bop_add_id_idempotent_check_correct. 
       rewrite bop_add_id_left_cancellative_check_correct. 
       rewrite bop_add_id_right_cancellative_check_correct. 
       rewrite bop_add_id_exists_ann_check_correct.
       reflexivity. 
Defined. 


Lemma correct_sg_C_certs_add_id : ∀ (s : S) (f : S -> S) (Pf : brel_not_trivial S r f) (P : sg_C_proofs S r b),
       sg_C_certs_add_id c s f (P2C_sg_C S r b P) 
       = 
       P2C_sg_C (with_constant S) 
                (brel_add_constant r c) 
                (bop_add_id b c) 
                (sg_C_proofs_add_id S r c b s f Pf Q P). 
Proof. intros s f Pf P. destruct P. destruct Q. 
       unfold sg_C_certs_add_id, sg_C_proofs_add_id, P2C_sg_C; simpl.
       rewrite bop_add_id_selective_check_correct. 
       rewrite bop_add_id_idempotent_check_correct. 
       rewrite bop_add_id_exists_ann_check_correct.
       rewrite bop_add_id_left_cancellative_check_correct. 
       rewrite bop_add_id_right_cancellative_check_correct. 
       reflexivity. 
Defined. 

Lemma correct_sg_CI_certs_add_id : ∀ (s : S) (P : sg_CI_proofs S r b), 
       sg_CI_certs_add_id c (P2C_sg_CI S r b P) 
       = 
       P2C_sg_CI (with_constant S) 
                 (brel_add_constant r c) 
                 (bop_add_id b c) 
                 (sg_CI_proofs_add_id S r c b s Q P). 
Proof. intros s P. destruct P. destruct Q. 
       unfold sg_CI_certs_add_id, sg_CI_proofs_add_id, P2C_sg_CI; simpl.
       rewrite bop_add_id_selective_check_correct. 
       rewrite bop_add_id_exists_ann_check_correct.
       reflexivity. 
Defined. 

Lemma correct_sg_CS_certs_add_id : ∀ (s : S) (P : sg_CS_proofs S r b),
       sg_CS_certs_add_id c (P2C_sg_CS S r b P) 
       = 
       P2C_sg_CS (with_constant S) 
                 (brel_add_constant r c) 
                 (bop_add_id b c) 
                 (sg_CS_proofs_add_id S r c b s Q P). 
Proof. intros s P. destruct P. destruct Q. 
       unfold sg_CS_certs_add_id, sg_CS_proofs_add_id, P2C_sg_CS ; simpl.
       rewrite bop_add_id_exists_ann_check_correct.
       reflexivity. 
Defined. 

End CertsCorrect.

Section AddAnnCorrect.

  Variable S : Type.
  Variable c : cas_constant. 

Theorem correct_sg_add_id  : ∀ (sgS : A_sg S), 
         sg_add_id c (A2C_sg S sgS) 
         = 
         A2C_sg (with_constant S) (A_sg_add_id S c sgS). 
Proof. intro sgS. 
       unfold sg_add_id, A2C_sg; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_certs_add_id. 
       reflexivity. 
Qed. 


Theorem correct_sg_C_add_id  : ∀ (sg_CS : A_sg_C S), 
         sg_C_add_id c (A2C_sg_C S sg_CS) 
         = 
         A2C_sg_C (with_constant S) (A_sg_C_add_id S c sg_CS). 
Proof. intro sg_CS. 
       unfold sg_C_add_id, A2C_sg_C; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_C_certs_add_id. 
       reflexivity. 
Qed. 

Theorem correct_sg_CI_add_id  : ∀ (sg_CIS : A_sg_CI S), 
         sg_CI_add_id c (A2C_sg_CI S sg_CIS) 
         = 
         A2C_sg_CI (with_constant S) (A_sg_CI_add_id S c sg_CIS). 
Proof. intro sg_CIS. 
       unfold sg_CI_add_id, A2C_sg_CI; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CI_certs_add_id. 
       reflexivity. 
Qed. 

Theorem correct_sg_CS_add_id  : ∀ (sg_CSS : A_sg_CS S), 
         sg_CS_add_id c (A2C_sg_CS S sg_CSS) 
         = 
         A2C_sg_CS (with_constant S) (A_sg_CS_add_id S c sg_CSS). 
Proof. intro sg_CSS. 
       unfold sg_CS_add_id, A2C_sg_CS; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CS_certs_add_id. 
       reflexivity. 
Qed. 

End AddAnnCorrect.