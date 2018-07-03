Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.combined. 
Require Import CAS.code.certificates.
Require Import CAS.code.cert_records.
Require Import CAS.code.construct_certs.
Require Import CAS.code.cast.
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.eq_list.
Require Import CAS.theory.bop.concat.
Require Import CAS.theory.bop.product. 
Require Import CAS.theory.bop.left_sum.
Require Import CAS.theory.bop.right_sum.
Require Import CAS.theory.brel.add_constant. 
Require Import CAS.theory.bop.add_ann.
Require Import CAS.theory.bop.add_id.
Require Import CAS.theory.bop.union. 
Require Import CAS.theory.bop.intersect. 
Require Import CAS.theory.bop.llex. 
Require Import CAS.theory.brel.product. 
Require Import CAS.theory.brel.sum. 

Require Import CAS.code.certificates. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.bs_properties. 
Require Import CAS.code.check. 
Require Import CAS.a_code.decide. 
Require Import CAS.verify.proofs_to_certs. 

Require Import CAS.a_code.proof_records.     (* ~~ cert_records *) 





(* 
   Need collection of lemmas of the form 

   CON_P_check_correct : 
   
   ∀ (q1 : Q1_decidable) (q2 : Q2_decidable) ... (qk : Qk_decidable), 
     
     p2c_P_check (CON_P_decide q1 q2 ... qk) 
     = 
     CON_P_check (p2C_Q1_check q1) (p2C_Q2_check q2) ... (p2C_Qk_check qk)

*) 



(* product product *) 


(* lex product *) 
Lemma bops_llex_product_left_distributive_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (eqvS : eqv_proofs S rS)
    (eqvT : eqv_proofs T rT)
    (sg_CS_S : sg_CS_proofs S rS plusS) 
    (sg_S : sg_proofs S rS timesS)
    (sg_C_T : sg_C_proofs T rT plusT)
    (sg_T : sg_proofs T rT timesT) 
    (pS_d : bop_left_distributive_decidable S rS plusS timesS) 
    (pT_d : bop_left_distributive_decidable T rT plusT timesT), 
  p2c_left_distributive (S * T) (brel_product S T rS rT)
     (bop_llex S T rS plusS plusT)
     (bop_product S T timesS timesT)
     (bops_llex_product_left_distributive_decide S T rS rT plusS timesS plusT timesT
        (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS))
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (A_eqv_transitive S rS eqvS)
        (A_sg_congruence S rS timesS sg_S)
        (A_sg_CS_selective S rS plusS sg_CS_S)
        (A_sg_CS_commutative S rS plusS sg_CS_S)
        (A_eqv_nontrivial T rT eqvT)
        (A_eqv_reflexive T rT eqvT)
        (A_eqv_symmetric T rT eqvT)
        (A_eqv_transitive T rT eqvT)
        (A_sg_C_commutative T rT plusT sg_C_T)
        (A_sg_left_cancel_d S rS timesS sg_S)
        (A_sg_left_constant_d T rT timesT sg_T) pS_d pT_d)
   = 
   bops_llex_product_left_distributive_check S T rS rT plusS plusT timesT 
      (p2c_nontrivial S rS (A_eqv_nontrivial S rS eqvS))
      (p2c_nontrivial T rT (A_eqv_nontrivial T rT eqvT))
      (p2c_left_cancel_check S rS timesS (A_sg_left_cancel_d S rS timesS sg_S))
      (p2c_left_constant_check T rT timesT (A_sg_left_constant_d T rT timesT sg_T))
      (p2c_left_distributive S rS plusS timesS pS_d)
      (p2c_left_distributive T rT plusT timesT pT_d).
Proof. intros S T rS rT plusS timesS plusT timesT eqvS eqvT. 
       destruct eqvS, eqvT.  
       destruct A_eqv_nontrivial  as [[s Ps] [f Pf]]. 
       destruct A_eqv_nontrivial0 as [[t Pt] [g Pg]]. simpl. 
       intros sg_CS_S sg_S sg_C_T sg_T.
       intros [ ldS | [ [s1 [s2 s3]] nldS]] 
              [ ldT | [ [t1 [t2 t3]] nldT]]; 
       destruct (A_sg_left_cancel_d S rS timesS sg_S) as [lcS | [ [s4 [s5 s6]] [L R]]]; 
       destruct (A_sg_left_constant_d T rT timesT sg_T) as [lkT | [ [t4 [t5 t6]] nlkS]]; 
       compute; reflexivity. 
Qed. 


Lemma bops_llex_product_right_distributive_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (eqvS : eqv_proofs S rS)
    (eqvT : eqv_proofs T rT)
    (sg_CS_S : sg_CS_proofs S rS plusS) 
    (sg_S : sg_proofs S rS timesS)
    (sg_C_T : sg_C_proofs T rT plusT)
    (sg_T : sg_proofs T rT timesT) 
    (pS_d : bop_right_distributive_decidable S rS plusS timesS) 
    (pT_d : bop_right_distributive_decidable T rT plusT timesT), 
  p2c_right_distributive (S * T) (brel_product S T rS rT)
     (bop_llex S T rS plusS plusT)
     (bop_product S T timesS timesT)
     (bops_llex_product_right_distributive_decide S T rS rT plusS timesS plusT timesT
        (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS))
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (A_eqv_transitive S rS eqvS)
        (A_sg_congruence S rS timesS sg_S)
        (A_sg_CS_selective S rS plusS sg_CS_S)
        (A_sg_CS_commutative S rS plusS sg_CS_S)
        (A_eqv_nontrivial T rT eqvT)
        (A_eqv_reflexive T rT eqvT)
        (A_eqv_symmetric T rT eqvT)
        (A_eqv_transitive T rT eqvT)
        (A_sg_C_commutative T rT plusT sg_C_T)
        (A_sg_right_cancel_d S rS timesS sg_S)
        (A_sg_right_constant_d T rT timesT sg_T) pS_d pT_d)
   = 
   bops_llex_product_right_distributive_check S T rS rT plusS plusT timesT 
      (p2c_nontrivial S rS (A_eqv_nontrivial S rS eqvS))
      (p2c_nontrivial T rT (A_eqv_nontrivial T rT eqvT))
      (p2c_right_cancel_check S rS timesS (A_sg_right_cancel_d S rS timesS sg_S))
      (p2c_right_constant_check T rT timesT (A_sg_right_constant_d T rT timesT sg_T))
      (p2c_right_distributive S rS plusS timesS pS_d)
      (p2c_right_distributive T rT plusT timesT pT_d).
Proof. intros S T rS rT plusS timesS plusT timesT eqvS eqvT.
       destruct eqvS, eqvT.  
       destruct A_eqv_nontrivial  as [[s Ps] [f Pf]]. 
       destruct A_eqv_nontrivial0 as [[t Pt] [g Pg]]. simpl. 
       intros sg_CS_S sg_S sg_C_T sg_T.
       intros [ ldS | [ [s1 [s2 s3]] nldS]] 
              [ ldT | [ [t1 [t2 t3]] nldT]]; 
       destruct (A_sg_right_cancel_d S rS timesS sg_S) as [lcS | [ [s4 [s5 s6]] [L R]]]; 
       destruct (A_sg_right_constant_d T rT timesT sg_T) as [lkT | [ [t4 [t5 t6]] nlkS]]; 
       compute; reflexivity. 
Qed. 


Lemma bops_llex_product_plus_id_is_times_ann_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (refS   : brel_reflexive S rS )
    (symS   : brel_symmetric S rS )
    (transS : brel_transitive S rS)
    (commS  : bop_commutative S rS plusS)
    (refT   : brel_reflexive T rT)
    (symT   : brel_symmetric T rT)
    (transT : brel_transitive T rT)
    (pS_d : bops_id_equals_ann_decidable S rS plusS timesS)
    (pT_d : bops_id_equals_ann_decidable T rT plusT timesT), 
   p2c_plus_id_equals_times_ann (S * T) 
      (brel_product S T rS rT)
      (bop_llex S T rS plusS plusT)
      (bop_product S T timesS timesT)
      (bops_llex_product_id_equals_ann_decide S T rS rT plusS timesS plusT timesT
         refS symS transS commS refT symT transT pS_d pT_d)
   = 
   bops_llex_product_plus_id_is_times_ann_check S T
      (p2c_plus_id_equals_times_ann S rS plusS timesS pS_d)
      (p2c_plus_id_equals_times_ann T rT plusT timesT pT_d). 
Proof. intros S T rS rT plusS timesS plusT timesT refS symS commS transS refT symT transT 
       [ eqS | neqS] [eqT | neqT] ; compute; reflexivity. 
Qed. 


Lemma bops_llex_product_times_id_equals_plus_ann_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (refS   : brel_reflexive S rS )
    (symS   : brel_symmetric S rS )
    (transS : brel_transitive S rS)
    (commS  : bop_commutative S rS plusS) 
    (refT   : brel_reflexive T rT)
    (symT   : brel_symmetric T rT)
    (transT : brel_transitive T rT)
    (pS_d : bops_id_equals_ann_decidable S rS timesS plusS)
    (pT_d : bops_id_equals_ann_decidable T rT timesT plusT), 
   p2c_times_id_equals_plus_ann (S * T) 
      (brel_product S T rS rT)
      (bop_llex S T rS plusS plusT)
      (bop_product S T timesS timesT)
      (bops_product_llex_id_equals_ann_decide S T rS rT plusS timesS plusT timesT
         refS symS transS commS refT symT transT pS_d pT_d)
   = 
   bops_llex_product_times_id_equals_plus_ann_check S T
      (p2c_times_id_equals_plus_ann S rS plusS timesS pS_d) 
      (p2c_times_id_equals_plus_ann T rT plusT timesT pT_d). 
Proof. intros S T rS rT plusS timesS plusT timesT refS symS transS commS refT symT transT 
       [ eqS | neqS] [eqT | neqT] ; compute; reflexivity. 
Qed. 


Lemma bops_llex_product_left_left_absorbtive_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (symS   : brel_symmetric S rS )
    (transS : brel_transitive S rS)
    (wtT : brel_witness T rT) 
    (refT   : brel_reflexive T rT)
    (pS_d : bops_left_left_absorptive_decidable S rS plusS timesS)
    (pT_d : bops_left_left_absorptive_decidable T rT  plusT timesT)
    (alS_d : bop_anti_left_decidable S rS timesS), 
   p2c_left_left_absorptive (S * T)
      (brel_product S T rS rT)
      (bop_llex S T rS plusS plusT)
      (bop_product S T timesS timesT)
      (bops_llex_product_left_left_absorptive_decide S T
         (brel_get_witness T rT wtT)
         rS rT plusS timesS plusT timesT symS transS refT pS_d pT_d alS_d)
   = 
   bops_llex_product_left_left_absorptive_check S T
      (projT1 wtT) 
      (p2c_left_left_absorptive S rS plusS timesS pS_d) 
      (p2c_left_left_absorptive T rT plusT timesT pT_d) 
      (p2c_anti_left_check S rS timesS alS_d). 
Proof. intros S T rS rT plusS timesS plusT timesT symS transS [t Pt] refT
       [ laS | [ [s1 s2] nlaS ] ]  [ laT | [ [t1 t2] nlaT ]]  [ alS | [ [s3 s4] nalS ]]; 
       compute; reflexivity. 
Qed. 


Lemma bops_llex_product_left_right_absorbtive_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (symS   : brel_symmetric S rS )
    (transS : brel_transitive S rS)
    (wtT : brel_witness T rT) 
    (refT   : brel_reflexive T rT)
    (pS_d : bops_left_right_absorptive_decidable S rS plusS timesS)
    (pT_d : bops_left_right_absorptive_decidable T rT  plusT timesT)
    (alS_d : bop_anti_right_decidable S rS timesS), 
   p2c_left_right_absorptive (S * T)
      (brel_product S T rS rT)
      (bop_llex S T rS plusS plusT)
      (bop_product S T timesS timesT)
      (bops_llex_product_left_right_absorptive_decide S T
         (brel_get_witness T rT wtT)
         rS rT plusS timesS plusT timesT symS transS refT pS_d pT_d alS_d)
   = 
   bops_llex_product_left_right_absorptive_check S T
      (projT1 wtT) 
      (p2c_left_right_absorptive S rS plusS timesS pS_d) 
      (p2c_left_right_absorptive T rT plusT timesT pT_d) 
      (p2c_anti_right_check S rS timesS alS_d). 
Proof. intros S T rS rT plusS timesS plusT timesT symS transS [t Pt] refT
       [ laS | [ [s1 s2] nlaS ] ]  [ laT | [ [t1 t2] nlaT ]]  [ alS | [ [s3 s4] nalS ]]; 
       compute; reflexivity. 
Qed. 



Lemma bops_llex_product_right_left_absorbtive_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (symS   : brel_symmetric S rS )
    (transS : brel_transitive S rS)
    (wtT : brel_witness T rT) 
    (refT   : brel_reflexive T rT)
    (pS_d : bops_right_left_absorptive_decidable S rS plusS timesS)
    (pT_d : bops_right_left_absorptive_decidable T rT  plusT timesT)
    (alS_d : bop_anti_left_decidable S rS timesS), 
   p2c_right_left_absorptive (S * T)
      (brel_product S T rS rT)
      (bop_llex S T rS plusS plusT)
      (bop_product S T timesS timesT)
      (bops_llex_product_right_left_absorptive_decide S T
         (brel_get_witness T rT wtT)
         rS rT plusS timesS plusT timesT symS transS refT pS_d pT_d alS_d)
   = 
   bops_llex_product_right_left_absorptive_check S T
      (projT1 wtT) 
      (p2c_right_left_absorptive S rS plusS timesS pS_d) 
      (p2c_right_left_absorptive T rT plusT timesT pT_d) 
      (p2c_anti_left_check S rS timesS alS_d). 
Proof. intros S T rS rT plusS timesS plusT timesT symS transS [t Pt] refT
       [ laS | [ [s1 s2] nlaS ] ]  [ laT | [ [t1 t2] nlaT ]]  [ alS | [ [s3 s4] nalS ]]; 
       compute; reflexivity. 
Qed. 



Lemma bops_llex_product_right_right_absorbtive_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (symS   : brel_symmetric S rS )
    (transS : brel_transitive S rS)
    (wtT : brel_witness T rT) 
    (refT   : brel_reflexive T rT)
    (pS_d : bops_right_right_absorptive_decidable S rS plusS timesS)
    (pT_d : bops_right_right_absorptive_decidable T rT  plusT timesT)
    (alS_d : bop_anti_right_decidable S rS timesS), 
   p2c_right_right_absorptive (S * T)
      (brel_product S T rS rT)
      (bop_llex S T rS plusS plusT)
      (bop_product S T timesS timesT)
      (bops_llex_product_right_right_absorptive_decide S T
         (brel_get_witness T rT wtT)
         rS rT plusS timesS plusT timesT symS transS refT pS_d pT_d alS_d)
   = 
   bops_llex_product_right_right_absorptive_check S T
      (projT1 wtT) 
      (p2c_right_right_absorptive S rS plusS timesS pS_d) 
      (p2c_right_right_absorptive T rT plusT timesT pT_d) 
      (p2c_anti_right_check S rS timesS alS_d). 
Proof. intros S T rS rT plusS timesS plusT timesT symS transS [t Pt] refT
       [ laS | [ [s1 s2] nlaS ] ]  [ laT | [ [t1 t2] nlaT ]]  [ alS | [ [s3 s4] nalS ]]; 
       compute; reflexivity. 
Qed. 









