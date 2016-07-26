Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.certificates.
Require Import CAS.code.cert_records.
Require Import CAS.code.check. 
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
Require Import CAS.theory.properties.        (* ~~ certificates *) 

Require Import CAS.a_code.decide.            (* ~~ code.check *) 
Require Import CAS.a_code.proof_records.     (* ~~ cert_records *) 
Require Import CAS.a_code.construct_proofs.  (* ~~ construct_certs *)
Require Import CAS.a_code.a_cast.
Require Import CAS.verify.proofs_to_certs. 
Require Import CAS.verify.check_correct. 

Theorem correct_eqv_certs_eq_bool : eqv_certs_eq_bool = P2C_eqv bool brel_eq_bool (eqv_proofs_eq_bool). 
Proof. compute. reflexivity. Defined. 

Theorem correct_eqv_eq_nat : eqv_certs_eq_nat = P2C_eqv nat brel_eq_nat (eqv_proofs_eq_nat). 
Proof. compute. reflexivity. Defined. 

Lemma correct_eqv_certs_brel_list : 
      ∀ (S : Type) (r : brel S) (P : eqv_proofs S r), 
       eqv_certs_brel_list S (P2C_eqv S r P) 
       = 
       P2C_eqv (list S) (brel_list S r) (eqv_proofs_brel_list S r P). 
Proof. intros S r P. destruct P. 
       destruct A_eqv_nontrivial. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. 
       compute. reflexivity. 
Defined. 


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



Lemma correct_eqv_certs_add_constant : 
      ∀ (S : Type) (r : brel S) (c : cas_constant) (P : eqv_proofs S r), 
       eqv_certs_add_constant S c (P2C_eqv S r P) 
       = 
       P2C_eqv (with_constant S) (brel_add_constant S r c) (eqv_proofs_add_constant S r c P). 
Proof. intros S r c P. destruct P. 
       unfold eqv_certs_add_constant, eqv_proofs_add_constant, P2C_eqv; simpl. 
       destruct A_eqv_nontrivial. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. 
       compute. reflexivity. 
Defined. 


Lemma correct_eqv_certs_product : 
      ∀ (S T : Type) (rS : brel S) (rT : brel T) (eS : eqv_proofs S rS) (eT : eqv_proofs T rT), 
       eqv_certs_product S T (P2C_eqv S rS eS) (P2C_eqv T rT eT) 
       = 
       P2C_eqv (S * T) (brel_product S T rS rT) (eqv_proofs_product S T rS rT eS eT). 
Proof. intros S T rS rT eS eT. destruct eS; destruct eT. 
       destruct A_eqv_nontrivial. 
       destruct A_eqv_nontrivial0. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. 
       destruct brel_nontrivial_witness0 as [t tP]. 
       destruct brel_nontrivial_negate0 as [g gP]. 
       compute. reflexivity. 
Defined. 

Lemma correct_eqv_certs_sum : 
      ∀ (S T : Type) (rS : brel S) (rT : brel T) (eS : eqv_proofs S rS) (eT : eqv_proofs T rT), 
       eqv_certs_sum S T (P2C_eqv S rS eS) (P2C_eqv T rT eT) 
       = 
       P2C_eqv (S + T) (brel_sum S T rS rT) (eqv_proofs_sum S T rS rT eS eT). 
Proof. intros S T rS rT eS eT. destruct eS; destruct eT. 
       destruct A_eqv_nontrivial. 
       destruct A_eqv_nontrivial0. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. 
       destruct brel_nontrivial_witness0 as [t tP]. 
       destruct brel_nontrivial_negate0 as [g gP]. 
       compute. reflexivity. 
Defined. 




(*                 ============ Semigroups ============                *) 


(* basics *) 

Lemma correct_sg_certs_left : 
      ∀ (S : Type) (r : brel S) (P : eqv_proofs S r), 
       sg_certs_left S (P2C_eqv S r P) 
       = 
       P2C_sg S r (bop_left S) (sg_proofs_left S r P). 
Proof. intros S r P. destruct P. 
       destruct A_eqv_nontrivial. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. 
       compute. reflexivity. 
Defined. 


Lemma correct_sg_certs_right : 
      ∀ (S : Type) (r : brel S) (P : eqv_proofs S r), 
       sg_certs_right S (P2C_eqv S r P) 
       = 
       P2C_sg S r (bop_right S) (sg_proofs_right S r P). 
Proof. intros S r P. destruct P. 
       destruct A_eqv_nontrivial. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. 
       compute. reflexivity. 
Defined. 


Lemma correct_sg_certs_concat : 
      ∀ (S : Type) (r : brel S) (P : eqv_proofs S r), 
       sg_certs_concat S (P2C_eqv S r P) 
       = 
       P2C_sg (list S) (brel_list S r) (bop_concat S) (sg_proofs_concat S r P). 
Proof. intros S r P. destruct P. 
       destruct A_eqv_nontrivial. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. 
       compute. reflexivity. 
Defined. 



(*                 ============ sg add_id ============                 *) 

Lemma correct_sg_certs_add_id : 
      ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) 
        (Q : eqv_proofs S r) (P : sg_proofs S r b), 
       sg_certs_add_id S c (P2C_eqv S r Q) (P2C_sg S r b P) 
       = 
       P2C_sg (with_constant S) 
          (brel_add_constant S r c) 
          (bop_add_id S b c) 
          (sg_proofs_add_id S r c b Q P). 
Proof. intros S r b c Q P. 
       (* destruct proof records *) 
       destruct P. destruct Q. 
       destruct A_eqv_nontrivial. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. simpl. 
       (* unfold transformations *) 
       unfold sg_proofs_add_id, P2C_sg, P2C_eqv, sg_certs_add_id; simpl. 
       (* rewrite attribute expressions *) 
       rewrite bop_add_id_commutative_check_correct. 
       rewrite bop_add_id_selective_check_correct. 
       rewrite bop_add_id_idempotent_check_correct. 
       rewrite bop_add_id_left_cancellative_check_correct. 
       rewrite bop_add_id_right_cancellative_check_correct. 
       rewrite bop_add_id_exists_ann_check_correct.
       reflexivity. 
Defined. 


Lemma correct_sg_C_certs_add_id : 
      ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) (Q : eqv_proofs S r) (P : sg_C_proofs S r b), 
       sg_C_certs_add_id S c (P2C_eqv S r Q) (P2C_sg_C S r b P) 
       = 
       P2C_sg_C (with_constant S) 
          (brel_add_constant S r c) 
          (bop_add_id S b c) 
          (sg_C_proofs_add_id S r c b Q P). 
Proof. intros S r b c Q P. destruct P. destruct Q. 
       destruct A_eqv_nontrivial. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. 
       unfold sg_C_certs_add_id, sg_C_proofs_add_id, P2C_sg_C, P2C_eqv; simpl.
       rewrite bop_add_id_selective_check_correct. 
       rewrite bop_add_id_idempotent_check_correct. 
       rewrite bop_add_id_exists_ann_check_correct.
       rewrite bop_add_id_left_cancellative_check_correct. 
       rewrite bop_add_id_right_cancellative_check_correct. 
       reflexivity. 
Defined. 


Lemma correct_sg_CI_certs_add_id : 
      ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) (Q : eqv_proofs S r) (P : sg_CI_proofs S r b), 
       sg_CI_certs_add_id S c (P2C_eqv S r Q) (P2C_sg_CI S r b P) 
       = 
       P2C_sg_CI (with_constant S) 
          (brel_add_constant S r c) 
          (bop_add_id S b c) 
          (sg_CI_proofs_add_id S r c b Q P). 
Proof. intros S r b c Q P. destruct P. destruct Q. 
       unfold sg_CI_certs_add_id, sg_CI_proofs_add_id, P2C_sg_CI, P2C_eqv; simpl.
       rewrite bop_add_id_selective_check_correct. 
       rewrite bop_add_id_exists_ann_check_correct.
       reflexivity. 
Defined. 


Lemma correct_sg_CS_certs_add_id : 
      ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) (Q : eqv_proofs S r) (P : sg_CS_proofs S r b), 
       sg_CS_certs_add_id S c (P2C_eqv S r Q) (P2C_sg_CS S r b P) 
       = 
       P2C_sg_CS (with_constant S) 
          (brel_add_constant S r c) 
          (bop_add_id S b c) 
          (sg_CS_proofs_add_id S r c b Q P). 
Proof. intros S r b c Q P. destruct P. destruct Q. 
       unfold sg_CS_certs_add_id, sg_CS_proofs_add_id, P2C_sg_CS, P2C_eqv; simpl.
       rewrite bop_add_id_exists_ann_check_correct.
       reflexivity. 
Defined. 


(*                 ============ sg add_ann ============                 *) 

Lemma correct_sg_certs_add_ann : 
      ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) (Q : eqv_proofs S r) (P : sg_proofs S r b), 
       sg_certs_add_ann S c (P2C_eqv S r Q) (P2C_sg S r b P) 
       = 
       P2C_sg (with_constant S) 
          (brel_add_constant S r c) 
          (bop_add_ann S b c) 
          (sg_proofs_add_ann S r c b Q P). 
Proof. intros S r b c Q P. 
       (* destruct proof records *) 
       destruct P. destruct Q. 
       destruct A_eqv_nontrivial. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. simpl. 
       (* unfold transformations *) 
       unfold sg_proofs_add_ann, P2C_sg, P2C_eqv, sg_certs_add_ann; simpl. 
       rewrite bop_add_ann_commutative_check_correct. 
       rewrite bop_add_ann_selective_check_correct. 
       rewrite bop_add_ann_idempotent_check_correct. 
       rewrite bop_add_ann_exists_id_check_correct.
       reflexivity. 
Defined. 


Lemma correct_sg_C_certs_add_ann : 
      ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) (Q : eqv_proofs S r) (P : sg_C_proofs S r b), 
       sg_C_certs_add_ann S c (P2C_eqv S r Q) (P2C_sg_C S r b P) 
       = 
       P2C_sg_C (with_constant S) 
          (brel_add_constant S r c) 
          (bop_add_ann S b c) 
          (sg_C_proofs_add_ann S r c b Q P). 
Proof. intros S r b c Q P. destruct P. destruct Q. 
       destruct A_eqv_nontrivial. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. simpl. 
       unfold sg_C_certs_add_ann, sg_C_proofs_add_ann, P2C_sg_C, P2C_eqv; simpl.
       rewrite bop_add_ann_selective_check_correct. 
       rewrite bop_add_ann_idempotent_check_correct. 
       rewrite bop_add_ann_exists_id_check_correct.
       reflexivity. 
Defined. 


Lemma correct_sg_CI_certs_add_ann : 
      ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) (Q : eqv_proofs S r) (P : sg_CI_proofs S r b), 
       sg_CI_certs_add_ann S c (P2C_eqv S r Q) (P2C_sg_CI S r b P) 
       = 
       P2C_sg_CI (with_constant S) 
          (brel_add_constant S r c) 
          (bop_add_ann S b c) 
          (sg_CI_proofs_add_ann S r c b Q P). 
Proof. intros S r b c Q P. destruct P. destruct Q. 
       unfold sg_CI_certs_add_ann, sg_CI_proofs_add_ann, P2C_sg_CI, P2C_eqv; simpl.
       rewrite bop_add_ann_selective_check_correct. 
       rewrite bop_add_ann_exists_id_check_correct.
       reflexivity. 
Defined. 


Lemma correct_sg_CS_certs_add_ann : 
      ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) (Q : eqv_proofs S r) (P : sg_CS_proofs S r b), 
       sg_CS_certs_add_ann S c (P2C_eqv S r Q) (P2C_sg_CS S r b P) 
       = 
       P2C_sg_CS (with_constant S) 
          (brel_add_constant S r c) 
          (bop_add_ann S b c) 
          (sg_CS_proofs_add_ann S r c b Q P). 
Proof. intros S r b c Q P. destruct P. destruct Q. 
       unfold sg_CS_certs_add_ann, sg_CS_proofs_add_ann, P2C_sg_CS, P2C_eqv; simpl.
       rewrite bop_add_ann_exists_id_check_correct.
       reflexivity. 
Defined. 

(* semigroup products *) 

Lemma correct_sg_certs_product : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_proofs S rS bS) 
        (pT : sg_proofs T rT bT),
      sg_certs_product S T (P2C_eqv S rS eS)
                           (P2C_eqv T rT eT) 
                           (P2C_sg S rS bS pS) 
                           (P2C_sg T rT bT pT) 
      = 
      P2C_sg (S * T) (brel_product S T rS rT) 
                     (bop_product S T bS bT) 
                     (sg_proofs_product S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT.
       unfold sg_proofs_product, sg_certs_product, P2C_sg, P2C_eqv; simpl. 
       rewrite correct_check_idempotent_product. 
       rewrite correct_check_is_right_product. 
       rewrite correct_check_is_left_product. 
       rewrite correct_check_commutative_product.
       rewrite correct_check_exists_id_product.  
       rewrite correct_check_exists_ann_product. 
       rewrite correct_check_selective_product. 
       rewrite correct_check_left_cancel_product. 
       rewrite correct_check_right_cancel_product. 
       rewrite correct_check_left_constant_product. 
       rewrite correct_check_right_constant_product. 
       rewrite correct_check_anti_left_product. 
       rewrite correct_check_anti_right_product. 
       reflexivity. 
Defined. 

(*
Lemma correct_sg_certs_product_new : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_proofs_new S rS bS) 
        (pT : sg_proofs_new T rT bT),
      sg_certs_product_new S T (P2C_eqv S rS eS)
                           (P2C_eqv T rT eT) 
                           (P2C_sg_new S rS bS pS) 
                           (P2C_sg_new T rT bT pT) 
      = 
      P2C_sg_new (S * T) (brel_product S T rS rT) 
                     (bop_product S T bS bT) 
                     (sg_proofs_product_new S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT.
       unfold sg_proofs_product_new, sg_certs_product_new, P2C_sg_new, P2C_eqv; simpl. 
       rewrite correct_check_idempotent_product_new. 
       rewrite correct_check_is_right_product_new. 
       rewrite correct_check_is_left_product_new. 
       rewrite correct_check_commutative_product_new.
       rewrite correct_check_exists_id_product_new.  
       rewrite correct_check_exists_ann_product_new. 
       rewrite correct_check_selective_product_new. 
       rewrite correct_check_left_cancel_product_new. 
       rewrite correct_check_right_cancel_product_new. 
       rewrite correct_check_left_constant_product_new. 
       rewrite correct_check_right_constant_product_new. 
       rewrite correct_check_anti_left_product_new. 
       rewrite correct_check_anti_right_product_new. 
       reflexivity. 
Defined. 
*) 

(* ????


Lemma  correct_sg_C_certs_product : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_C_proofs S rS bS) 
        (pT : sg_C_proofs T rT bT),
      sg_C_certs_product S T rS rT bS bT 
         (P2C_eqv S rS eS)
         (P2C_eqv T rT eT) 
         (P2C_sg_C S rS bS pS) 
         (P2C_sg_C T rT bT pT) 
      = 
      P2C_sg_C (S * T) 
         (brel_product S T rS rT) 
         (bop_product S T bS bT) 
         (sg_C_proofs_product S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT.
       unfold sg_proofs_product, sg_certs_product, P2C_sg, P2C_eqv; simpl. 
       rewrite correct_check_idempotent_product. 
       rewrite correct_check_is_right_product. 
       rewrite correct_check_is_left_product. 
       rewrite correct_check_commutative_product.
       rewrite correct_check_exists_id_product.  
       rewrite correct_check_exists_ann_product. 
       rewrite correct_check_selective_product. 
       rewrite correct_check_left_cancel_product. 
       rewrite correct_check_right_cancel_product. 
       rewrite correct_check_left_constant_product. 
       rewrite correct_check_right_constant_product. 
       rewrite correct_check_anti_left_product. 
       rewrite correct_check_anti_right_product. 
       reflexivity. 
Defined. 

*) 


Lemma  correct_sg_CK_certs_product : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_CK_proofs S rS bS) 
        (pT : sg_CK_proofs T rT bT),
      sg_CK_certs_product S T 
         (P2C_eqv S rS eS)
         (P2C_eqv T rT eT) 
         (P2C_sg_CK S rS bS pS) 
         (P2C_sg_CK T rT bT pT) 
      = 
      P2C_sg_CK (S * T) 
         (brel_product S T rS rT) 
         (bop_product S T bS bT) 
         (sg_CK_proofs_product S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT.
       unfold sg_CK_proofs_product, sg_CK_certs_product, P2C_sg_CK, P2C_eqv; simpl. 
       rewrite correct_check_exists_id_product.  
       rewrite correct_check_anti_left_product. 
       rewrite correct_check_anti_right_product. 
       reflexivity. 
Defined. 


(* semigroup lexicographic *)   

Lemma correct_sg_certs_llex : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_CS_proofs S rS bS) 
        (pT : sg_proofs T rT bT),
      sg_certs_llex S T rS bS (P2C_eqv S rS eS)
                           (P2C_eqv T rT eT) 
                           (P2C_sg_CS S rS bS pS) 
                           (P2C_sg T rT bT pT) 
      = 
      P2C_sg (S * T) (brel_product S T rS rT) 
                     (bop_llex S T rS bS bT) 
                     (sg_proofs_llex S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT.
       unfold sg_proofs_llex, sg_certs_llex, P2C_sg, P2C_sg_CS, P2C_eqv; simpl. 
       rewrite correct_check_idempotent_llex. 
       rewrite correct_check_commutative_llex.
       rewrite correct_check_exists_id_llex.  
       rewrite correct_check_exists_ann_llex. 
       rewrite correct_check_selective_llex. 
       rewrite correct_not_left_cancellative_llex.
       rewrite correct_not_right_cancellative_llex.
       rewrite correct_not_left_constant_llex.
       rewrite correct_not_right_constant_llex.
       rewrite correct_not_anti_left_llex.
       rewrite correct_not_anti_right_llex.
       rewrite correct_not_is_left_llex.
       rewrite correct_not_is_right_llex.
       reflexivity. 
Defined. 


Lemma correct_sg_C_certs_llex : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_CS_proofs S rS bS) 
        (pT : sg_C_proofs T rT bT),
      sg_C_certs_llex S T rS bS (P2C_eqv S rS eS)
                           (P2C_eqv T rT eT) 
                           (P2C_sg_CS S rS bS pS) 
                           (P2C_sg_C T rT bT pT) 
      = 
      P2C_sg_C (S * T) (brel_product S T rS rT) 
                     (bop_llex S T rS bS bT) 
                     (sg_C_proofs_llex S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT.
       unfold sg_C_proofs_llex, sg_C_certs_llex, P2C_sg_C, P2C_sg_CS, P2C_eqv; simpl. 
       rewrite correct_check_exists_id_llex.  
       rewrite correct_check_exists_ann_llex. 
       rewrite correct_check_idempotent_llex. 
       rewrite correct_check_selective_llex. 
       rewrite correct_not_left_constant_llex.
       rewrite correct_not_right_constant_llex.
       rewrite correct_not_anti_left_llex.
       rewrite correct_not_anti_right_llex.
       rewrite correct_not_left_cancellative_llex.
       rewrite correct_not_right_cancellative_llex.
       reflexivity. 
Defined. 


Lemma correct_sg_CI_certs_llex : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_CS_proofs S rS bS) 
        (pT : sg_CI_proofs T rT bT),
      sg_CI_certs_llex S T rS bS (P2C_eqv S rS eS)
                           (P2C_eqv T rT eT) 
                           (P2C_sg_CS S rS bS pS) 
                           (P2C_sg_CI T rT bT pT) 
      = 
      P2C_sg_CI (S * T) (brel_product S T rS rT) 
                     (bop_llex S T rS bS bT) 
                     (sg_CI_proofs_llex S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT.
       unfold sg_CI_proofs_llex, sg_CI_certs_llex, P2C_sg_CI, P2C_sg_CS, P2C_eqv; simpl. 
       rewrite correct_check_exists_id_llex.  
       rewrite correct_check_exists_ann_llex. 
       rewrite correct_check_selective_llex. 
       reflexivity. 
Defined. 


Lemma correct_sg_CS_certs_llex : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_CS_proofs S rS bS) 
        (pT : sg_CS_proofs T rT bT),
      sg_CS_certs_llex S T rS bS (P2C_eqv S rS eS)
                           (P2C_eqv T rT eT) 
                           (P2C_sg_CS S rS bS pS) 
                           (P2C_sg_CS T rT bT pT) 
      = 
      P2C_sg_CS (S * T) (brel_product S T rS rT) 
                     (bop_llex S T rS bS bT) 
                     (sg_CS_proofs_llex S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT.
       unfold sg_CS_proofs_llex, sg_CS_certs_llex, P2C_sg_CS, P2C_eqv; simpl. 
       rewrite correct_check_exists_id_llex.  
       rewrite correct_check_exists_ann_llex. 
       reflexivity. 
Defined. 



(* semigroup sums  *) 
Lemma correct_sg_certs_left_sum : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_proofs S rS bS) 
        (pT : sg_proofs T rT bT),
      sg_certs_left_sum S T (P2C_eqv S rS eS)
                           (P2C_eqv T rT eT) 
                           (P2C_sg S rS bS pS) 
                           (P2C_sg T rT bT pT) 
      = 
      P2C_sg (S + T) (brel_sum S T rS rT) 
                     (bop_left_sum S T bS bT) 
                     (sg_proofs_left_sum S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT. 
       unfold sg_proofs_left_sum, sg_certs_left_sum, P2C_sg, P2C_eqv; simpl. 
       rewrite <- correct_check_commutative_left_sum. 
       rewrite <- correct_check_selective_left_sum. 
       rewrite correct_check_idempotent_left_sum. 
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum. 

       (* ugly ugly ugly ! *) 
       destruct A_eqv_nontrivial, A_eqv_nontrivial0. 
       destruct brel_nontrivial_witness as [s sP]; 
       destruct brel_nontrivial_witness0 as [t tP]; simpl.  
       destruct brel_nontrivial_negate as [f fP]; 
       destruct brel_nontrivial_negate0 as [g gP]; simpl.  
       unfold p2c_nontrivial, nontrivial_witness, p2c_negate, p2c_witness, nontrivial_negate; simpl. 
       destruct (gP t) as [L1 R1]; destruct (fP s) as [L2 R2].
       reflexivity. 
Defined. 

Lemma correct_sg_certs_right_sum : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_proofs S rS bS) 
        (pT : sg_proofs T rT bT),
      sg_certs_right_sum S T (P2C_eqv S rS eS)
                           (P2C_eqv T rT eT) 
                           (P2C_sg S rS bS pS) 
                           (P2C_sg T rT bT pT) 
      = 
      P2C_sg (S + T) (brel_sum S T rS rT) 
                     (bop_right_sum S T bS bT) 
                     (sg_proofs_right_sum S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT. 
       unfold sg_proofs_right_sum, sg_certs_right_sum, P2C_sg, P2C_eqv; simpl. 
       rewrite <- correct_check_commutative_right_sum. 
       rewrite <- correct_check_selective_right_sum. 
       rewrite correct_check_idempotent_right_sum. 
       rewrite <- correct_check_exists_id_right_sum. 
       rewrite <- correct_check_exists_ann_right_sum. 

       (* ugly ugly ugly ! *) 
       destruct A_eqv_nontrivial, A_eqv_nontrivial0. 
       destruct brel_nontrivial_witness as [s sP]; 
       destruct brel_nontrivial_witness0 as [t tP]; simpl.  
       destruct brel_nontrivial_negate as [f fP]; 
       destruct brel_nontrivial_negate0 as [g gP]; simpl.  
       unfold p2c_nontrivial, nontrivial_witness, p2c_negate, p2c_witness, nontrivial_negate; simpl. 
       destruct (gP t) as [L1 R1]; destruct (fP s) as [L2 R2].
       reflexivity. 
Defined. 



Lemma correct_sg_C_certs_left_sum : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_C_proofs S rS bS) 
        (pT : sg_C_proofs T rT bT),
      sg_C_certs_left_sum S T (P2C_eqv S rS eS)
                           (P2C_eqv T rT eT) 
                           (P2C_sg_C S rS bS pS) 
                           (P2C_sg_C T rT bT pT) 
      = 
      P2C_sg_C (S + T) (brel_sum S T rS rT) 
                     (bop_left_sum S T bS bT) 
                     (sg_C_proofs_left_sum S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT. 
       unfold sg_C_proofs_left_sum, sg_C_certs_left_sum, P2C_sg_C, P2C_eqv; simpl. 
       rewrite <- correct_check_selective_left_sum. 
       rewrite correct_check_idempotent_left_sum. 
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum. 

       (* ugly ugly ugly ! *) 
       destruct A_eqv_nontrivial, A_eqv_nontrivial0. 
       destruct brel_nontrivial_witness as [s sP]; 
       destruct brel_nontrivial_witness0 as [t tP]; 
       destruct brel_nontrivial_negate as [f fP]; 
       destruct brel_nontrivial_negate0 as [g gP]; simpl.  
       unfold p2c_nontrivial, nontrivial_witness, p2c_negate, p2c_witness, nontrivial_negate; simpl. 
       destruct (gP t) as [L1 R1]; destruct (fP s) as [L2 R2].
       reflexivity. 
Defined. 



Lemma correct_sg_C_certs_right_sum : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_C_proofs S rS bS) 
        (pT : sg_C_proofs T rT bT),
      sg_C_certs_right_sum S T (P2C_eqv S rS eS)
                           (P2C_eqv T rT eT) 
                           (P2C_sg_C S rS bS pS) 
                           (P2C_sg_C T rT bT pT) 
      = 
      P2C_sg_C (S + T) (brel_sum S T rS rT) 
                     (bop_right_sum S T bS bT) 
                     (sg_C_proofs_right_sum S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT. 
       unfold sg_C_proofs_right_sum, sg_C_certs_right_sum, P2C_sg_C, P2C_eqv; simpl.        
       rewrite <- correct_check_selective_right_sum. 
       rewrite correct_check_idempotent_right_sum. 
       rewrite <- correct_check_exists_id_right_sum. 
       rewrite <- correct_check_exists_ann_right_sum. 

       (* ugly ugly ugly ! *) 
       destruct A_eqv_nontrivial, A_eqv_nontrivial0. 
       destruct brel_nontrivial_witness as [s sP]; 
       destruct brel_nontrivial_witness0 as [t tP]; simpl.  
       destruct brel_nontrivial_negate as [f fP]; 
       destruct brel_nontrivial_negate0 as [g gP]; simpl.  
       unfold p2c_nontrivial, nontrivial_witness, p2c_negate, p2c_witness, nontrivial_negate; simpl. 
       destruct (gP t) as [L1 R1]; destruct (fP s) as [L2 R2].
       reflexivity. 
Defined. 


Lemma correct_sg_CS_certs_left_sum : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_CS_proofs S rS bS) 
        (pT : sg_CS_proofs T rT bT),
      sg_CS_certs_left_sum S T (P2C_eqv S rS eS)
                           (P2C_eqv T rT eT) 
                           (P2C_sg_CS S rS bS pS) 
                           (P2C_sg_CS T rT bT pT) 
      = 
      P2C_sg_CS (S + T) (brel_sum S T rS rT) 
                     (bop_left_sum S T bS bT) 
                     (sg_CS_proofs_left_sum S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT. 
       unfold sg_CS_proofs_left_sum, sg_CS_certs_left_sum, P2C_sg_CS, P2C_eqv; simpl. 
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum. 
       reflexivity. 
Defined. 


Lemma correct_sg_CS_certs_right_sum : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_CS_proofs S rS bS) 
        (pT : sg_CS_proofs T rT bT),
      sg_CS_certs_right_sum S T (P2C_eqv S rS eS)
                           (P2C_eqv T rT eT) 
                           (P2C_sg_CS S rS bS pS) 
                           (P2C_sg_CS T rT bT pT) 
      = 
      P2C_sg_CS (S + T) (brel_sum S T rS rT) 
                     (bop_right_sum S T bS bT) 
                     (sg_CS_proofs_right_sum S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT. 
       unfold sg_CS_proofs_right_sum, sg_CS_certs_right_sum, P2C_sg_CS, P2C_eqv; simpl.        
       rewrite <- correct_check_exists_id_right_sum. 
       rewrite <- correct_check_exists_ann_right_sum. 
       reflexivity. 
Defined. 


Lemma correct_sg_CI_certs_left_sum : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_CI_proofs S rS bS) 
        (pT : sg_CI_proofs T rT bT),
      sg_CI_certs_left_sum S T (P2C_eqv S rS eS)
                           (P2C_eqv T rT eT) 
                           (P2C_sg_CI S rS bS pS) 
                           (P2C_sg_CI T rT bT pT) 
      = 
      P2C_sg_CI (S + T) (brel_sum S T rS rT) 
                     (bop_left_sum S T bS bT) 
                     (sg_CI_proofs_left_sum S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT. 
       unfold sg_CI_proofs_left_sum, sg_CI_certs_left_sum, P2C_sg_CI, P2C_eqv; simpl. 
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum. 
       rewrite <- correct_check_selective_left_sum. 
       reflexivity. 
Defined. 



Lemma correct_sg_CI_certs_right_sum : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (eS : eqv_proofs S rS) 
        (eT : eqv_proofs T rT)
        (pS : sg_CI_proofs S rS bS) 
        (pT : sg_CI_proofs T rT bT),
      sg_CI_certs_right_sum S T (P2C_eqv S rS eS)
                           (P2C_eqv T rT eT) 
                           (P2C_sg_CI S rS bS pS) 
                           (P2C_sg_CI T rT bT pT) 
      = 
      P2C_sg_CI (S + T) (brel_sum S T rS rT) 
                     (bop_right_sum S T bS bT) 
                     (sg_CI_proofs_right_sum S T rS rT bS bT eS eT pS pT). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct pS; destruct pT; destruct eS; destruct eT. 
       unfold sg_CI_proofs_right_sum, sg_CI_certs_right_sum, P2C_sg_CI, P2C_eqv; simpl. 
       rewrite <- correct_check_exists_id_right_sum. 
       rewrite <- correct_check_exists_ann_right_sum. 
       rewrite <- correct_check_selective_right_sum. 
       reflexivity. 
Defined. 



(* SETS *) 

(* 
Lemma correct_sg_CI_certs_union_with_ann : 
      ∀ (S : Type) (c : cas_constant) (r : brel S) (Q : eqv_proofs S r), 
       sg_certs_union S c (P2C_eqv S r Q) 
       = 
       P2C_sg (with_constant (finite_set S)) 
          (brel_add_constant (finite_set S) (brel_set S r) c) 
          (bop_add_ann (finite_set S) (bop_union S r) c)
          (sg_proofs_union S r c Q). 
Proof. intros S c r Q. destruct Q. 
       destruct A_eqv_nontrivial. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. 
       unfold sg_certs_union, sg_CI_proofs_union, P2C_sg, P2C_eqv; simpl.
       reflexivity. 
Defined. 


Lemma correct_sg_certs_intersect_with_id : 
      ∀ (S : Type) (c : cas_constant) (r : brel S) (Q : eqv_proofs S r), 
       sg_certs_intersect_with_id S c (P2C_eqv S r Q) 
       = 
       P2C_sg (with_constant (finite_set S)) 
          (brel_add_constant (finite_set S) (brel_set S r) c) 
          (bop_add_id (finite_set S) (bop_intersect S r) c)
          (sg_proofs_intersect_with_id S r c Q). 
Proof. intros S c r Q. destruct Q. 
       destruct A_eqv_nontrivial. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. 
       unfold sg_certs_intersect, sg_proofs_intersect, P2C_sg, P2C_eqv;
       compute;     destruct (fP s) as [L R]; 
       reflexivity. 
Defined. 

*) 

(* SG SG 

Lemma  correct_sg_sg_certs_add_zero : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) 
    (plusS timesS : binary_op S) 
    (eqvS : eqv_proofs S rS)
    (sg_sgS : sg_sg_proofs S rS plusS timesS), 
    P2C_sg_sg (with_constant S) 
       (brel_add_constant S rS c) 
       (bop_add_id S plusS c) 
       (bop_add_ann S timesS c) 
       (sg_sg_proofs_add_zero S rS c plusS timesS eqvS sg_sgS)
    =
    sg_sg_certs_add_zero S (P2C_eqv S rS eqvS) (P2C_sg_sg S rS plusS timesS sg_sgS). 
Proof. intros S c rS plusS timesS eqvS sg_sgS. 
       unfold sg_sg_certs_add_zero, sg_sg_proofs_add_zero, P2C_sg_sg; simpl. 
       rewrite bops_add_zero_left_distributive_check_correct. 
       rewrite bops_add_zero_right_distributive_check_correct. 
       rewrite bops_add_zero_times_id_equals_plus_ann_check_correct.
       rewrite (bops_add_zero_left_absorbtive_check_correct S c rS plusS timesS eqvS). 
       rewrite (bops_add_zero_right_absorbtive_check_correct S c rS plusS timesS eqvS). 
       reflexivity. 
Defined. 


Lemma  correct_sg_sg_certs_add_one : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) 
    (plusS timesS : binary_op S) 
    (eqvS : eqv_proofs S rS)
    (sgS : sg_C_proofs S rS plusS) 
    (sg_sgS : sg_sg_proofs S rS plusS timesS), 
    P2C_sg_sg (with_constant S) 
       (brel_add_constant S rS c) 
       (bop_add_ann S plusS c) 
       (bop_add_id S timesS c) 
       (sg_sg_proofs_add_one S rS c plusS timesS eqvS sgS sg_sgS)
    =
    sg_sg_certs_add_one S c (P2C_eqv S rS eqvS) (P2C_sg_C S rS plusS sgS) (P2C_sg_sg S rS plusS timesS sg_sgS). 
Proof. intros S c rS plusS timesS eqvS sgS sg_sgS. 
       unfold sg_sg_certs_add_one, sg_sg_proofs_add_one, P2C_sg_sg, P2C_eqv, P2C_sg_C; simpl. 
       rewrite bops_add_one_left_distributive_check_correct. 
       rewrite bops_add_one_right_distributive_check_correct. 
       rewrite bops_add_one_plus_id_equals_times_ann_check_correct.
       rewrite (bops_add_one_left_absorbtive_check_correct S c rS plusS timesS 
                  (A_eqv_reflexive S rS eqvS)). 
       rewrite (bops_add_one_right_absorbtive_check_correct S c rS plusS timesS 
                  (A_eqv_reflexive S rS eqvS)). 
       reflexivity. 
       apply (A_sg_C_commutative S rS plusS sgS). 
       apply (A_sg_C_commutative S rS plusS sgS). 
Defined. 



Lemma  correct_sg_sg_certs_product : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (eqvS : eqv_proofs S rS)
    (eqvT :  eqv_proofs T rT)
    (sg_sgS : sg_sg_proofs S rS plusS timesS)
    (sg_sgT : sg_sg_proofs T rT plusT timesT), 
    sg_sg_certs_product S T 
       (P2C_eqv S rS eqvS) 
       (P2C_eqv T rT eqvT) 
       (P2C_sg_sg S rS plusS timesS sg_sgS) 
       (P2C_sg_sg T rT plusT timesT sg_sgT)
    =
    P2C_sg_sg (S * T) 
       (brel_product S T rS rT) 
       (bop_product S T plusS plusT) 
       (bop_product S T timesS timesT) 
       (sg_sg_proofs_product S T rS rT plusS timesS plusT timesT eqvS eqvT sg_sgS sg_sgT). 
Proof. intros S T rS rT plusS timesS plusT timesT eqvS eqvT sg_sgS sg_sgT. 
       unfold sg_sg_certs_product, sg_sg_proofs_product, P2C_sg_sg; simpl. 
       rewrite bop_product_left_distributive_check_correct. 
       rewrite bop_product_right_distributive_check_correct. 
       rewrite bop_product_plus_id_is_times_ann_check_correct. 
       rewrite bop_product_times_id_equals_plus_ann_check_correct.
       rewrite bop_product_left_absorbtive_check_correct. 
       rewrite bop_product_right_absorbtive_check_correct. 
       reflexivity. 
Defined. 


Lemma  correct_sg_sg_certs_llex_product : 
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
    (sg_sgS : sg_sg_proofs S rS plusS timesS)
    (sg_sgT : sg_sg_proofs T rT plusT timesT), 
    P2C_sg_sg (S * T) 
       (brel_product S T rS rT) 
       (bop_llex S T rS plusS plusT) 
       (bop_product S T timesS timesT) 
       (sg_sg_proofs_llex S T rS rT plusS timesS plusT timesT eqvS eqvT 
	sg_CS_S sg_S sg_C_T sg_T sg_sgS sg_sgT) 
    =
    sg_sg_certs_llex_product S T rS rT plusS plusT timesT
       (P2C_eqv S rS eqvS) 
       (P2C_eqv T rT eqvT) 
       (P2C_sg S rS timesS sg_S) 
       (P2C_sg T rT timesT sg_T) 
       (P2C_sg_sg S rS plusS timesS sg_sgS) 
       (P2C_sg_sg T rT plusT timesT sg_sgT). 
Proof. intros S T rS rT plusS timesS plusT timesT eqvS eqvT sg_CS_S sg_S sg_C_T sg_T sg_sgS sg_sgT. 
       unfold sg_sg_certs_llex_product, sg_sg_proofs_llex. 
       unfold P2C_sg_sg; simpl. 
       rewrite bops_llex_product_left_distributive_check_correct. 
       rewrite bops_llex_product_right_distributive_check_correct. 
       rewrite bops_llex_product_plus_id_is_times_ann_check_correct. 
       rewrite bops_llex_product_times_id_equals_plus_ann_check_correct.
       rewrite bops_llex_product_left_absorbtive_check_correct. 
       rewrite bops_llex_product_right_absorbtive_check_correct. 
       reflexivity. 
Defined. 


*) 