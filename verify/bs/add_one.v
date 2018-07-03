Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.bop.

Require Import CAS.code.bs_certificates. 
Require Import CAS.code.bs_cert_records.

Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.

Require Import CAS.code.cas.bs.add_one.
Require Import CAS.a_code.a_cas.bs.add_one. 

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


Lemma bops_add_one_plus_id_equals_times_ann_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_id_equals_ann_decidable S rS plusS timesS), 
  p2c_plus_id_equals_times_ann (with_constant S)
     (brel_add_constant rS c)
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_id_equals_ann_decide S rS 
        c plusS timesS s (A_eqv_reflexive S rS eqvS) pS) 
  =  bops_plus_id_equals_times_ann_check c (p2c_plus_id_equals_times_ann S rS plusS timesS pS).
Proof. intros S c rS s plusS timesS eqvS [ L | R]; compute; reflexivity. Qed. 
 

Lemma bops_add_one_left_distributive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS)     
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (llaS_d : bops_left_left_absorptive_decidable S rS plusS timesS) 
  (rlaS_d : bops_right_left_absorptive_decidable S rS plusS timesS) 
  (ldS_d : bop_left_distributive_decidable S rS plusS timesS), 
  p2c_left_distributive (with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_left_distributive_decide S rS c plusS timesS 
         (A_eqv_reflexive S rS eqvS) (A_eqv_symmetric S rS eqvS) idmS_d llaS_d rlaS_d ldS_d)
  = 
  bops_add_one_left_distributive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_left_absorptive S rS plusS timesS llaS_d)
     (p2c_right_left_absorptive S rS plusS timesS rlaS_d)
     (p2c_left_distributive S rS plusS timesS ldS_d). 
Proof. intros S c rS plusS timesS eqvS
       [ idmS | [ s0 nidmS ] ] 
       [ llaS | [ [s1 s2] nllaS ] ]
       [ rlaS | [ [s6 s7] nrlaS ] ]
       [ ldS | [ [s3 [s4 s5]] nldS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma bops_add_one_right_distributive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS)         
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (llaS_d : bops_left_right_absorptive_decidable S rS plusS timesS) 
  (rlaS_d : bops_right_right_absorptive_decidable S rS plusS timesS) 
  (ldS_d : bop_right_distributive_decidable S rS plusS timesS), 
  p2c_right_distributive (with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_right_distributive_decide S rS c plusS timesS 
       (A_eqv_reflexive S rS eqvS) (A_eqv_symmetric S rS eqvS) idmS_d llaS_d rlaS_d ldS_d)
  = 
  bops_add_one_right_distributive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_right_absorptive S rS plusS timesS llaS_d)
     (p2c_right_right_absorptive S rS plusS timesS rlaS_d)
     (p2c_right_distributive S rS plusS timesS ldS_d). 
Proof. intros S c rS plusS timesS eqvS
       [ idmS | [ s0 nidmS ] ] 
       [ llaS | [ [s1 s2] nllaS ] ]
       [ rlaS | [ [s6 s7] nrlaS ] ]
       [ ldS | [ [s3 [s4 s5]] nldS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma bops_add_one_left_left_absorbtive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS)             
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_left_left_absorptive_decidable S rS plusS timesS), 
  p2c_left_left_absorptive (with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_left_left_absorptive_decide S rS c plusS timesS (A_eqv_symmetric S rS eqvS) idmS_d laS_d)
  = 
  bops_add_one_left_left_absorptive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_left_absorptive S rS plusS timesS laS_d).
Proof. intros S c rS plusS timesS eqvS 
       [ idmS | [ s0 nidmS ] ] 
       [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma bops_add_one_left_right_absorbtive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS)                 
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_left_right_absorptive_decidable S rS plusS timesS), 
  p2c_left_right_absorptive (with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_left_right_absorptive_decide S rS c plusS timesS (A_eqv_symmetric S rS eqvS) idmS_d laS_d)
  = 
  bops_add_one_left_right_absorptive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_right_absorptive S rS plusS timesS laS_d).
Proof. intros S c rS plusS timesS eqvS 
       [ idmS | [ s0 nidmS ] ] 
       [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma bops_add_one_right_left_absorbtive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS)                     
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_right_left_absorptive_decidable S rS plusS timesS), 
  p2c_right_left_absorptive (with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_right_left_absorptive_decide S rS c plusS timesS (A_eqv_symmetric S rS eqvS) idmS_d laS_d)
  = 
  bops_add_one_right_left_absorptive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_right_left_absorptive S rS plusS timesS laS_d).
Proof. intros S c rS plusS timesS eqvS 
       [ idmS | [ s0 nidmS ] ] 
       [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma bops_add_one_right_right_absorbtive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS)                     
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_right_right_absorptive_decidable S rS plusS timesS), 
  p2c_right_right_absorptive (with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_right_right_absorptive_decide S rS c plusS timesS (A_eqv_symmetric S rS eqvS) idmS_d laS_d)
  = 
  bops_add_one_right_right_absorptive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_right_right_absorptive S rS plusS timesS laS_d).
Proof. intros S c rS plusS timesS eqvS 
       [ idmS | [ s0 nidmS ] ] 
       [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma  correct_bs_certs_add_one : 
  ∀ (S : Type) (c : cas_constant) (s : S) (rS : brel S) 
    (plusS timesS : binary_op S) 
    (eqvS : eqv_proofs S rS)
    (sgS : sg_proofs S rS plusS) 
    (bsS : bs_proofs S rS plusS timesS), 
    P2C_bs (with_constant S) 
       (brel_add_constant rS c) 
       (bop_add_ann plusS c) 
       (bop_add_id timesS c) 
       (bs_proofs_add_one S rS c plusS timesS s eqvS sgS bsS)
    =
    bs_certs_add_one c (P2C_sg S rS plusS sgS) (P2C_bs S rS plusS timesS bsS). 
Proof. intros S c s rS plusS timesS eqvS sgS bsS. 
       unfold bs_certs_add_one, bs_proofs_add_one, P2C_bs, P2C_sg; simpl. 
       rewrite bops_add_one_left_distributive_check_correct. 
       rewrite bops_add_one_right_distributive_check_correct. 
       rewrite bops_add_one_plus_id_equals_times_ann_check_correct.
       rewrite bops_add_one_left_left_absorbtive_check_correct .
       rewrite bops_add_one_left_right_absorbtive_check_correct. 
       rewrite bops_add_one_right_left_absorbtive_check_correct. 
       rewrite bops_add_one_right_right_absorbtive_check_correct. 
       reflexivity. 
Defined. 

Theorem correct_bs_add_one : ∀ (S : Type) (bsS: A_bs S) (c : cas_constant), 
   bs_add_one (A2C_bs S bsS) c 
   =
   A2C_bs (with_constant S) (A_bs_add_one S bsS c). 
Proof. intros S bsS c. 
       unfold bs_add_one, A_bs_add_one, A2C_bs; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_certs_add_ann. 
       rewrite <- correct_sg_certs_add_id. 
       rewrite correct_bs_certs_add_one. 
       reflexivity. 
Qed. 


Lemma bops_add_one_left_distributive_dual_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
    (eqvS : eqv_proofs S rS)
  (idmS_d : bop_idempotent_decidable S rS timesS) 
  (llaS_d : bops_left_left_absorptive_decidable S rS timesS plusS ) 
  (rlaS_d : bops_right_left_absorptive_decidable S rS timesS plusS ) 
  (ldS_d : bop_left_distributive_decidable S rS timesS plusS ),     
  p2c_left_distributive_dual (with_constant S)
     (brel_add_constant rS c)
     (bop_add_ann plusS c)
     (bop_add_id timesS c)                        
     (bops_add_zero_left_distributive_decide S rS c timesS plusS 
         (A_eqv_reflexive S rS eqvS) ldS_d)
  = 
  bops_add_one_left_distributive_dual_check 
     (p2c_left_distributive_dual S rS plusS timesS ldS_d). 
Proof. intros S c rS plusS timesS eqvS
       [ idmS | [ s0 nidmS ] ] 
       [ llaS | [ [s1 s2] nllaS ] ]
       [ rlaS | [ [s6 s7] nrlaS ] ]
       [ ldS | [ [s3 [s4 s5]] nldS ] ]; 
       compute; reflexivity. 
Qed. 




Require Import CAS.theory.facts. (* broken abstraction below! *) 

Lemma  correct_lattice_certs_add_one : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) 
    (join meet : binary_op S) 
    (eqvS : eqv_proofs S rS)
    (pjoin : sg_CI_proofs S rS join)
    (pmeet : sg_CI_proofs S rS meet)     
    (latticeS : lattice_proofs S rS join meet), 
    P2C_lattice (with_constant S) 
       (brel_add_constant rS c) 
       (bop_add_ann join c) 
       (bop_add_id meet c) 
       (lattice_proofs_add_one S rS c join meet eqvS pjoin pmeet latticeS)
    =
    lattice_certs_add_one c (P2C_lattice S rS join meet latticeS). 
Proof. intros S c rS join meet eqvS pjoin pmeet latticeS. 
       unfold lattice_certs_add_one, lattice_proofs_add_one, P2C_lattice, P2C_sg; simpl. 
       rewrite bops_add_one_left_distributive_dual_check_correct.
       rewrite bops_add_one_left_distributive_check_correct. simpl. 
       reflexivity.
       (* ugly!  Broken abstraction! where? *)
       destruct pmeet. left; auto.
       destruct latticeS. left; auto.        
       destruct latticeS. left; auto.
       destruct eqvS, pmeet, pjoin.  
       apply bops_left_right_absorptive_implies_right_left; auto.
       apply bops_left_left_absorptive_implies_left_right; auto.        
Qed. 

Theorem correct_lattice_add_one : ∀ (S : Type) (latticeS: A_lattice S) (c : cas_constant), 
   lattice_add_one S (A2C_lattice S latticeS) c 
   =
   A2C_lattice (with_constant S) (A_lattice_add_one S latticeS c). 
Proof. intros S latticeS c. 
       unfold lattice_add_one, A_lattice_add_one, A2C_lattice; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CI_certs_add_ann. 
       rewrite <- correct_sg_CI_certs_add_id. 
       rewrite correct_lattice_certs_add_one. 
       reflexivity. 
Qed. 


Lemma  correct_distributive_lattice_certs_add_one : 
  ∀ (S : Type) (rS : brel S) (join meet : binary_op S) (c:  cas_constant) 
    (eqvS : eqv_proofs S rS) 
    (pjoin : sg_CI_proofs S rS join)
    (pmeet : sg_CI_proofs S rS meet)
    (dlp : distributive_lattice_proofs S rS join meet), 

    P2C_distributive_lattice _ _ _ _ (distributive_lattice_proofs_add_one S rS c join meet eqvS pjoin pmeet dlp) 
    =
    distributive_lattice_certs_add_one c (P2C_distributive_lattice S rS join meet dlp). 
Proof. intros S rS join meet c eqvS pjoin pmeet dlp. compute. reflexivity. Qed.

Theorem correct_distributive_lattice_add_one : ∀ (S : Type) (distributive_latticeS: A_distributive_lattice S) (c : cas_constant), 
   distributive_lattice_add_one S (A2C_distributive_lattice S distributive_latticeS) c 
   =
   A2C_distributive_lattice (with_constant S) (A_distributive_lattice_add_one S distributive_latticeS c). 
Proof. intros S distributive_latticeS c. 
       unfold distributive_lattice_add_one, A_distributive_lattice_add_one, A2C_distributive_lattice; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CI_certs_add_ann. 
       rewrite <- correct_sg_CI_certs_add_id. 
       rewrite correct_distributive_lattice_certs_add_one. 
       reflexivity. 
Qed. 
