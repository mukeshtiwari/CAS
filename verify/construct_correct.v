Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.combined. 
Require Import CAS.code.certificates. 
Require Import CAS.code.cert_records.
Require Import CAS.code.check. 
Require Import CAS.code.construct_certs.
Require Import CAS.code.cast.
Require Import CAS.a_code.proof_records.     
Require Import CAS.a_code.construct_proofs.  
Require Import CAS.a_code.a_cast.
Require Import CAS.verify.proofs_to_certs. 
Require Import CAS.verify.check_correct. 

Lemma correct_eqv_certs_brel_set : 
      ∀ (S : Type) (r : brel S) (P : eqv_proofs S r), 
       eqv_certs_brel_set S r (P2C_eqv S r P) 
       = 
       P2C_eqv (finite_set S) (brel_set S r) (eqv_proofs_brel_set S r P). 
Proof. intros S r P. destruct P. 
       destruct A_eqv_nontrivial. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. 
       compute. reflexivity. 
Defined. 






(*                 ============ Orders ============                    *) 

Lemma correct_certs_to_dual : ∀ (S : Type) (eq lte : brel S) (p : to_proofs S eq lte ), 
   to_certs_dual S (P2C_to S eq lte p) 
   = 
   P2C_to S eq (brel_dual S lte) (to_proofs_dual S eq lte p). 
Proof. intros S eq lte p. compute. reflexivity. Qed. 


Lemma correct_certs_po_dual : ∀ (S : Type)  (eq lte : brel S) (p : po_proofs S eq lte ), 
   po_certs_dual S (P2C_po S eq lte p) 
   = 
   P2C_po S eq (brel_dual S lte) (po_proofs_dual S eq lte p). 
Proof. intros S eq lte p. destruct p. destruct A_po_total_d. 
       compute. reflexivity. 
       compute. destruct b as [[s t] P]. 
       reflexivity. 
Qed. 

Lemma correct_certs_to_rlte : ∀ (S : Type) (eq : brel S) (b : binary_op S) 
                                (eqv : eqv_proofs S eq) (p : sg_CS_proofs S eq b), 
   to_certs_rlte S (P2C_eqv S eq eqv) (P2C_sg_CS S eq b p) 
   = 
   P2C_to S eq (brel_rlte S eq b) (to_proofs_rlte S eq b eqv p). 
Proof. intros S eq b eqv p. compute. reflexivity. Qed. 

Lemma correct_certs_to_llte : ∀ (S : Type) (eq : brel S) (b : binary_op S) 
                                (eqv : eqv_proofs S eq) (p : sg_CS_proofs S eq b), 
   to_certs_llte S (P2C_eqv S eq eqv) (P2C_sg_CS S eq b p) 
   = 
   P2C_to S eq (brel_llte S eq b) (to_proofs_llte S eq b eqv p). 
Proof. intros S eq b eqv p. compute. reflexivity. Qed. 


Lemma correct_certs_po_llte : ∀ (S : Type) (eq : brel S) (b : binary_op S) 
                                (eqv : eqv_proofs S eq) (p : sg_CI_proofs S eq b), 
   po_certs_llte S (P2C_eqv S eq eqv) (P2C_sg_CI S eq b p) 
   = 
   P2C_po S eq (brel_llte S eq b) (po_proofs_llte S eq b eqv p). 
Proof. intros S eq b eqv p.  destruct p.  
       destruct A_sg_CI_selective_d. 
         compute. reflexivity. 
         destruct b0 as [[s t] P]. compute. reflexivity. 
Qed. 


Lemma correct_certs_po_rlte : ∀ (S : Type) (eq : brel S) (b : binary_op S) 
                                (eqv : eqv_proofs S eq) (p : sg_CI_proofs S eq b), 
   po_certs_rlte S (P2C_eqv S eq eqv) (P2C_sg_CI S eq b p) 
   = 
   P2C_po S eq (brel_rlte S eq b) (po_proofs_rlte S eq b eqv p). 
Proof. intros S eq b eqv p.  destruct p.  
       destruct A_sg_CI_selective_d. 
         compute. reflexivity. 
         destruct b0 as [[s t] P]. compute. reflexivity. 
Qed.






Lemma  correct_bs_certs_llex_product :
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (eqvS : eqv_proofs S rS)
    (eqvT :  eqv_proofs T rT)
    (sg_CS_S : sg_CS_proofs S rS plusS) 
    (sg_S : sg_proofs S rS timesS)
    (sg_C_T : sg_C_proofs T rT plusT)
    (sg_T : sg_proofs T rT timesT) 
    (bsS : bs_proofs S rS plusS timesS)
    (bsT : bs_proofs T rT plusT timesT), 
    P2C_bs (S * T) 
       (brel_product S T rS rT) 
       (bop_llex S T rS plusS plusT) 
       (bop_product S T timesS timesT) 
       (bs_proofs_llex S T rS rT plusS timesS plusT timesT eqvS eqvT 
	sg_CS_S sg_S sg_C_T sg_T bsS bsT) 
    =
    bs_certs_llex_product S T rS rT plusS plusT timesT
       (P2C_eqv S rS eqvS) 
       (P2C_eqv T rT eqvT) 
       (P2C_sg S rS timesS sg_S) 
       (P2C_sg T rT timesT sg_T) 
       (P2C_bs S rS plusS timesS bsS) 
       (P2C_bs T rT plusT timesT bsT). 
Proof. intros S T rS rT plusS timesS plusT timesT eqvS eqvT sg_CS_S sg_S sg_C_T sg_T bsS bsT. 
       unfold bs_certs_llex_product, bs_proofs_llex. 
       unfold P2C_bs; simpl. 
       rewrite bops_llex_product_left_distributive_check_correct. 
       rewrite bops_llex_product_right_distributive_check_correct. 
       rewrite bops_llex_product_plus_id_is_times_ann_check_correct. 
       rewrite bops_llex_product_times_id_equals_plus_ann_check_correct.
       rewrite bops_llex_product_left_left_absorbtive_check_correct. 
       rewrite bops_llex_product_left_right_absorbtive_check_correct. 
       rewrite bops_llex_product_right_left_absorbtive_check_correct. 
       rewrite bops_llex_product_right_right_absorbtive_check_correct. 
       reflexivity. 
Defined. 


