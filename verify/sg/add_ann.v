Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.bop.

Require Import CAS.code.sg_certificates. 
Require Import CAS.code.sg_cert_records.
Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.

Require Import CAS.code.cas.sg.add_ann.
Require Import CAS.a_code.a_cas.sg.add_ann. 

Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.bop.add_ann. 

Require Import CAS.verify.eqv.add_constant. 
Require Import CAS.verify.eqv_proofs_to_certs.
Require Import CAS.verify.sg_proofs_to_certs.

Section CertsCorrect. 

  Variable S : Type.
  Variable r : brel S.
  Variable b : binary_op S.
  Variable c : cas_constant. 
  Variable Q : eqv_proofs S r. 
  
Lemma bop_add_ann_commutative_check_correct : ∀ p_d : bop_commutative_decidable S r b, 
     p2c_commutative_check (with_constant S)
                         (brel_add_constant r c) 
                         (bop_add_ann b c)
                         (bop_add_ann_commutative_decide S r c b p_d)
     =                          
     bop_add_ann_commutative_check (p2c_commutative_check S r b p_d). 
Proof. intros [p | [ [s1 s2] np]]; compute; reflexivity. Qed. 


Lemma bop_add_ann_selective_check_correct : ∀ p_d : bop_selective_decidable S r b, 
     p2c_selective_check (with_constant S)
                         (brel_add_constant r c) 
                         (bop_add_ann b c)
                         (bop_add_ann_selective_decide S r c b p_d)
     =                          
     bop_add_ann_selective_check (p2c_selective_check S r b p_d). 
Proof. intros [p | [ [s1 s2] np]]; compute; reflexivity. Qed. 

Lemma bop_add_ann_idempotent_check_correct : ∀ p_d : bop_idempotent_decidable S r b,       
     p2c_idempotent_check (with_constant S)
                         (brel_add_constant r c) 
                         (bop_add_ann b c)
                         (bop_add_ann_idempotent_decide S r c b p_d)
     =                          
     bop_add_ann_idempotent_check (p2c_idempotent_check S r b p_d). 
Proof. intros [p | [s np] ]; compute; reflexivity. Qed. 

Lemma bop_add_ann_exists_id_check_correct : ∀ (s : S) (p_d : bop_exists_id_decidable S r b),
    p2c_exists_id_check (with_constant S)
                        (brel_add_constant r c)
                        (bop_add_ann b c)
                        (bop_add_ann_exists_id_decide S r c b s p_d)
     =                          
     bop_add_ann_exists_id_check (p2c_exists_id_check S r b p_d). 
Proof. intros s [ [a p] | np ]; compute; reflexivity. Qed.


Lemma correct_sg_certs_add_ann : ∀ (s : S) (f : S-> S) (Pf : brel_not_trivial S r f) (P : sg_proofs S r b), 
       sg_certs_add_ann c s f (P2C_sg S r b P) 
       = 
       P2C_sg (with_constant S) 
          (brel_add_constant r c) 
          (bop_add_ann b c) 
          (sg_proofs_add_ann S r c b s f Pf Q P). 
Proof. intros s f Pf P. 
       destruct P. destruct Q. 
       unfold sg_proofs_add_ann, P2C_sg, sg_certs_add_ann; simpl. 
       rewrite bop_add_ann_commutative_check_correct. 
       rewrite bop_add_ann_selective_check_correct. 
       rewrite bop_add_ann_idempotent_check_correct. 
       rewrite bop_add_ann_exists_id_check_correct.
       reflexivity. 
Defined. 

Lemma correct_sg_C_certs_add_ann : ∀ (s : S) (f : S-> S) (Pf : brel_not_trivial S r f) (P : sg_C_proofs S r b), 
       sg_C_certs_add_ann  c s f (P2C_sg_C S r b P) 
       = 
       P2C_sg_C (with_constant S) 
          (brel_add_constant r c) 
          (bop_add_ann b c) 
          (sg_C_proofs_add_ann S r c b s f Pf Q P). 
Proof. intros s f Pf P. destruct P. destruct Q. 
       unfold sg_C_certs_add_ann, sg_C_proofs_add_ann, P2C_sg_C; simpl.
       rewrite bop_add_ann_selective_check_correct. 
       rewrite bop_add_ann_idempotent_check_correct. 
       rewrite bop_add_ann_exists_id_check_correct.
       reflexivity. 
Defined. 


Lemma correct_sg_CI_certs_add_ann : ∀ (s : S) (P : sg_CI_proofs S r b), 
       sg_CI_certs_add_ann c (P2C_sg_CI S r b P) 
       = 
       P2C_sg_CI (with_constant S) 
          (brel_add_constant r c) 
          (bop_add_ann b c) 
          (sg_CI_proofs_add_ann S r c b s Q P). 
Proof. intros s P. destruct P. destruct Q. 
       unfold sg_CI_certs_add_ann, sg_CI_proofs_add_ann, P2C_sg_CI; simpl.
       rewrite bop_add_ann_selective_check_correct. 
       rewrite bop_add_ann_exists_id_check_correct.
       reflexivity. 
Defined. 


Lemma correct_sg_CS_certs_add_ann : ∀ (s : S) (P : sg_CS_proofs S r b), 
       sg_CS_certs_add_ann c  (P2C_sg_CS S r b P) 
       = 
       P2C_sg_CS (with_constant S) 
          (brel_add_constant r c) 
          (bop_add_ann b c) 
          (sg_CS_proofs_add_ann S r c b s Q P). 
Proof. intros s P. destruct P. destruct Q. 
       unfold sg_CS_certs_add_ann, sg_CS_proofs_add_ann, P2C_sg_CS; simpl.
       rewrite bop_add_ann_exists_id_check_correct.
       reflexivity. 
Defined.

End CertsCorrect. 

Section AddAnnCorrect.

  Variable S : Type.
  Variable c : cas_constant. 
  

Theorem correct_sg_add_ann  : ∀ (sgS : A_sg S), 
         sg_add_ann c (A2C_sg S sgS) 
         = 
         A2C_sg (with_constant S) (A_sg_add_ann S c sgS). 
Proof. intro sgS. unfold A2C_sg, sg_add_ann; simpl.
       rewrite <- correct_sg_certs_add_ann. 
       rewrite correct_eqv_add_constant. 
       reflexivity. 
Qed. 

Theorem correct_sg_C_add_ann  : ∀ (sg_CS : A_sg_C S), 
         sg_C_add_ann c (A2C_sg_C S sg_CS) 
         = 
         A2C_sg_C (with_constant S) (A_sg_C_add_ann S c sg_CS). 
Proof. intro sg_CS. unfold sg_C_add_ann, A2C_sg_C; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_C_certs_add_ann. 
       reflexivity. 
Qed. 

Theorem correct_sg_CI_add_ann  : ∀ (sg_CIS : A_sg_CI S), 
         sg_CI_add_ann c (A2C_sg_CI S sg_CIS) 
         = 
         A2C_sg_CI (with_constant S) (A_sg_CI_add_ann S c sg_CIS). 
Proof. intro sg_CIS. unfold sg_CI_add_ann, A2C_sg_CI; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CI_certs_add_ann. 
       reflexivity. 
Qed. 

Theorem correct_sg_CS_add_ann  : ∀ (sg_CSS : A_sg_CS S), 
         sg_CS_add_ann c (A2C_sg_CS S sg_CSS) 
         = 
         A2C_sg_CS (with_constant S) (A_sg_CS_add_ann S c sg_CSS). 
Proof. intro sg_CSS. unfold sg_CS_add_ann, A2C_sg_CS; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CS_certs_add_ann. 
       reflexivity. 
Qed. 

End AddAnnCorrect.