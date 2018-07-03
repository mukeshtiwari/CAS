
Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.bop.

Require Import CAS.code.bs_certificates. 
Require Import CAS.code.bs_cert_records.

Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.

Require Import CAS.a_code.a_cas.bs.add_zero. 
Require Import CAS.code.cas.bs.add_zero.

Require Import CAS.theory.bop_properties.
Require Import CAS.theory.bs_properties. 
Require Import CAS.theory.bs.add_ann_add_id. 
Require Import CAS.theory.bs.add_id_add_ann. 

Require Import CAS.verify.eqv_proofs_to_certs.
Require Import CAS.verify.sg_proofs_to_certs.
Require Import CAS.verify.bs_proofs_to_certs.

Require Import CAS.verify.eqv.add_constant. 
Require Import CAS.verify.sg.add_id.
Require Import CAS.verify.sg.add_ann. 


Lemma bops_add_zero_left_distributive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS)     
  (pS : bop_left_distributive_decidable S rS plusS timesS), 
  p2c_left_distributive (with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (bops_add_zero_left_distributive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_left_distributive_check (p2c_left_distributive S rS plusS timesS pS). 
Proof. intros S c rS plusS timesS eqvS [ ldS | [ [s1 [s2 s3]] nldS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma  bops_add_zero_right_distributive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
    (eqvS : eqv_proofs S rS)         
    (pS : bop_right_distributive_decidable S rS plusS timesS), 
  p2c_right_distributive (with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (bops_add_zero_right_distributive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_right_distributive_check (p2c_right_distributive S rS plusS timesS pS). 
Proof. intros S c rS plusS timesS eqvS [ ldS | [ [s1 [s2 s3]] nldS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma bops_add_zero_times_id_equals_plus_ann_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_id_equals_ann_decidable S rS timesS plusS), 
  p2c_times_id_equals_plus_ann (with_constant S)
     (brel_add_constant rS c)
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (bops_add_zero_ann_equals_id_decide S rS c 
        plusS timesS s (A_eqv_reflexive S rS eqvS) pS) 
  =
  bops_add_zero_times_id_is_plus_ann_check (p2c_times_id_equals_plus_ann S rS plusS timesS pS). 
Proof. intros S c rS s plusS timesS eqvS [ L | R]; compute; reflexivity. Qed. 



Lemma bops_add_zero_left_left_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_left_left_absorptive_decidable S rS plusS timesS), 
  p2c_left_left_absorptive(with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (bops_add_zero_left_left_absorptive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_left_left_absorptive_check s 
     (p2c_left_left_absorptive S rS plusS timesS pS). 
Proof. intros S c rS s plusS timesS eqvS [ ldS | [ [s1 s2] nldS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma bops_add_zero_left_right_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_left_right_absorptive_decidable S rS plusS timesS), 
  p2c_left_right_absorptive(with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (bops_add_zero_left_right_absorptive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_left_right_absorptive_check s (p2c_left_right_absorptive S rS plusS timesS pS).
Proof. intros S c rS s plusS timesS eqvS [ ldS | [ [s1 s2] nldS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma  bops_add_zero_right_left_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_right_left_absorptive_decidable S rS plusS timesS), 
  p2c_right_left_absorptive(with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (bops_add_zero_right_left_absorptive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_right_left_absorptive_check s (p2c_right_left_absorptive S rS plusS timesS pS). 
Proof. intros S c rS s plusS timesS eqvS [ ldS | [ [s1 s2] nldS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma  bops_add_zero_right_right_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_right_right_absorptive_decidable S rS plusS timesS), 
  p2c_right_right_absorptive(with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (bops_add_zero_right_right_absorptive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_right_right_absorptive_check  s (p2c_right_right_absorptive S rS plusS timesS pS). 
Proof. intros S c rS s plusS timesS eqvS [ ldS | [ [s1 s2] nldS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma  correct_bs_certs_add_zero : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) 
    (plusS timesS : binary_op S) 
    (eqvS : eqv_proofs S rS)
    (bsS : bs_proofs S rS plusS timesS), 
    P2C_bs (with_constant S) 
       (brel_add_constant rS c) 
       (bop_add_id plusS c) 
       (bop_add_ann timesS c) 
       (bs_proofs_add_zero S rS c plusS timesS s eqvS bsS)
    =
    bs_certs_add_zero s (P2C_bs S rS plusS timesS bsS). 
Proof. intros S c rS s plusS timesS eqvS bsS. 
       unfold bs_certs_add_zero, bs_proofs_add_zero, P2C_bs, P2C_sg; simpl. 
       rewrite bops_add_zero_left_distributive_check_correct. 
       rewrite bops_add_zero_right_distributive_check_correct. 
       rewrite bops_add_zero_times_id_equals_plus_ann_check_correct.
       rewrite (bops_add_zero_left_left_absorbtive_check_correct S c rS s plusS timesS eqvS). 
       rewrite (bops_add_zero_left_right_absorbtive_check_correct S c rS s plusS timesS eqvS). 
       rewrite (bops_add_zero_right_left_absorbtive_check_correct S c rS s plusS timesS eqvS). 
       rewrite (bops_add_zero_right_right_absorbtive_check_correct S c rS s plusS timesS eqvS). 
       reflexivity. 
Defined. 

Theorem correct_bs_add_zero: ∀ (S : Type) (bsS: A_bs S) (c : cas_constant), 
   bs_add_zero (A2C_bs S bsS) c 
   =
   A2C_bs (with_constant S) (A_bs_add_zero S bsS c). 
Proof. intros S bsS c. 
       unfold bs_add_zero, A_bs_add_zero, A2C_bs; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_certs_add_ann. 
       rewrite <- correct_sg_certs_add_id. 
       rewrite correct_bs_certs_add_zero. 
       reflexivity. 
Qed. 

Lemma  correct_semiring_certs_add_zero : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) 
    (plusS timesS : binary_op S) 
    (eqvS : eqv_proofs S rS)
    (bsS : semiring_proofs S rS plusS timesS), 
    P2C_semiring (with_constant S) 
       (brel_add_constant rS c) 
       (bop_add_id plusS c) 
       (bop_add_ann timesS c) 
       (semiring_proofs_add_zero S rS c plusS timesS s eqvS bsS)
    =
    semiring_certs_add_zero s (P2C_semiring S rS plusS timesS bsS). 
Proof. intros S c rS s plusS timesS eqvS bsS. 
       unfold semiring_certs_add_zero, semiring_proofs_add_zero, P2C_semiring, P2C_sg; simpl. 
       rewrite bops_add_zero_times_id_equals_plus_ann_check_correct.
       rewrite (bops_add_zero_left_left_absorbtive_check_correct S c rS s plusS timesS eqvS). 
       rewrite (bops_add_zero_left_right_absorbtive_check_correct S c rS s plusS timesS eqvS). 
       reflexivity. 
Defined. 


Theorem correct_semiring_add_zero: ∀ (S : Type) (pS: A_semiring S) (c : cas_constant), 
   semiring_add_zero S (A2C_semiring S pS) c 
   =
   A2C_semiring (with_constant S) (A_semiring_add_zero S pS c). 
Proof. intros S pS c. 
       unfold semiring_add_zero, A_semiring_add_zero, A2C_semiring; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_certs_add_ann. 
       rewrite <- correct_sg_C_certs_add_id. 
       rewrite correct_semiring_certs_add_zero. 
       reflexivity. 
Qed. 


Theorem correct_dioid_add_zero: ∀ (S : Type) (pS: A_dioid S) (c : cas_constant), 
   dioid_add_zero S (A2C_dioid S pS) c 
   =
   A2C_dioid (with_constant S) (A_dioid_add_zero S pS c). 
Proof. intros S pS c. 
       unfold dioid_add_zero, A_dioid_add_zero, A2C_dioid; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_certs_add_ann. 
       rewrite <- correct_sg_CI_certs_add_id. 
       rewrite correct_semiring_certs_add_zero. 
       reflexivity. 
Qed. 

Lemma  correct_distributive_lattice_certs_add_zero : 
  ∀ (S : Type) (rS : brel S) (join meet : binary_op S) (c:  cas_constant) 
    (eqvS : eqv_proofs S rS) 
    (pmeet : sg_CI_proofs S rS meet)
    (dlp : distributive_lattice_proofs S rS join meet), 
    P2C_distributive_lattice _ _ _ _ (distributive_lattice_proofs_add_zero S rS c join meet eqvS pmeet dlp)
    =
    distributive_lattice_certs_add_zero c (P2C_distributive_lattice S rS join meet dlp).
Proof. intros S rS join meet c eqvS pmeet dlp. compute. reflexivity. Qed.

Theorem correct_distributive_lattice_add_zero : ∀ (S : Type) (distributive_latticeS: A_distributive_lattice S) (c : cas_constant), 
   distributive_lattice_add_zero S (A2C_distributive_lattice S distributive_latticeS) c 
   =
   A2C_distributive_lattice (with_constant S) (A_distributive_lattice_add_zero S distributive_latticeS c). 
Proof. intros S distributive_latticeS c. 
       unfold distributive_lattice_add_zero, A_distributive_lattice_add_zero, A2C_distributive_lattice; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CI_certs_add_ann. 
       rewrite <- correct_sg_CI_certs_add_id. 
       rewrite correct_distributive_lattice_certs_add_zero. 
       reflexivity. 
Qed. 


Lemma  correct_lattice_certs_add_zero : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) 
    (joinS meetS : binary_op S) 
    (eqvS : eqv_proofs S rS)
    (pjoin : sg_CI_proofs S rS joinS)
    (pmeet : sg_CI_proofs S rS meetS) 
    (bsS : lattice_proofs S rS joinS meetS), 
    P2C_lattice (with_constant S) 
       (brel_add_constant rS c) 
       (bop_add_id joinS c) 
       (bop_add_ann meetS c) 
       (lattice_proofs_add_zero S rS c joinS meetS eqvS pjoin pmeet bsS)
    =
    lattice_certs_add_zero (P2C_lattice S rS joinS meetS bsS). 
Proof. intros S c rS s joinS meetS eqvS pjoin pmeet bsS. 
       unfold lattice_certs_add_zero, lattice_proofs_add_zero, P2C_lattice, P2C_sg; simpl. 
       rewrite bops_add_zero_left_distributive_check_correct.
       (* below, ugly! what is broken? *) 
       unfold bops_add_one_left_distributive_decide; simpl.
       unfold bops_add_zero_distributive_dual_check.
       case_eq (A_lattice_distributive_dual_d S rS joinS meetS bsS); intros b P; simpl. 
       reflexivity.
       destruct b as [ [s1 [s2 s3]] Q]. simpl. 
       reflexivity.        
Defined. 
