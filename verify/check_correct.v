Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
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
Require Import CAS.theory.properties.        (* ~~ certificates *) 
Require Import CAS.code.check. 
Require Import CAS.a_code.decide. 
Require Import CAS.verify.proofs_to_certs. 

Require Import CAS.a_code.proof_records.     (* ~~ cert_records *) 

(* 
Require Import CAS.a_code.construct_proofs.  (* ~~ construct_certs *)
Require Import CAS.a_code.a_cast.
*) 


(* bop product *) 

Lemma correct_check_commutative_product : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (dS : bop_commutative_decidable S rS bS)
         (dT : bop_commutative_decidable T rT bT),
         check_commutative_product S T 
            (p2c_nontrivial S rS ntS) 
            (p2c_nontrivial T rT ntT) 
            (p2c_commutative_check S rS bS dS)
            (p2c_commutative_check T rT bT dT)
         = 
         p2c_commutative_check (S * T) 
            (brel_product S T rS rT) 
            (bop_product S T bS bT)
            (bop_product_commutative_decide S T rS rT bS bT ntS ntT dS dT). 
Proof. intros S T rS rT bS bT ntS ntT. 
       destruct ntS as [[s sP] [f fP]]. destruct ntT as [[t tP] [g gP]]. 
       intros [cS | [ [s3 s4] ncS] ] [cT | [ [t3 t4] ncT] ]; 
       compute; reflexivity. 
Defined. 


(*
Lemma correct_check_commutative_product_new : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (dS : bop_commutative_decidable_new S rS bS)
         (dT : bop_commutative_decidable_new T rT bT),
         check_commutative_product_new S T 
            (nontrivial_witness S (p2c_nontrivial S rS ntS)) 
            (nontrivial_witness T (p2c_nontrivial T rT ntT))
            (projT1 dS)
            (projT1 dT)
         = 
         projT1 (bop_product_commutative_decide_new S T rS rT bS bT ntS ntT dS dT). 
Proof. intros S T rS rT bS bT 
              [[s sP] [f fP]] 
              [[t tP] [g gP]] 
              [ [uS | [s3 s4]] cS ] 
              [ [uT | [t3 t4]] cT ]; 
       compute; reflexivity. 
Defined. 
*) 


Lemma correct_check_is_left_product : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (dS : bop_is_left_decidable S rS bS)
         (dT : bop_is_left_decidable T rT bT),
         check_is_left_product S T 
            (p2c_nontrivial S rS ntS) 
            (p2c_nontrivial T rT ntT) 
            (p2c_is_left_check S rS bS dS)
            (p2c_is_left_check T rT bT dT)
         = 
         p2c_is_left_check (S * T) 
            (brel_product S T rS rT) 
            (bop_product S T bS bT)
            (bop_product_is_left_decide S T rS rT bS bT ntS ntT dS dT). 
Proof. intros S T rS rT bS bT ntS ntT. 
       destruct ntS as [[s sP] [f fP]]. destruct ntT as [[t tP] [g gP]]. 
       intros [cS | [ [s3 s4] ncS ] ] [cT | [ [t3 t4] ncT ]]; 
       compute; reflexivity. 
Defined. 

(*
Lemma correct_check_is_left_product_new : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (dS : bop_is_left_decidable_new S rS bS)
         (dT : bop_is_left_decidable_new T rT bT),
         check_is_left_product_new S T 
            (nontrivial_witness S (p2c_nontrivial S rS ntS))
            (nontrivial_witness T (p2c_nontrivial T rT ntT)) 
            (projT1 dS)
            (projT1 dT)
         = 
         projT1 (bop_product_is_left_decide_new S T rS rT bS bT ntS ntT dS dT). 
Proof. intros S T rS rT bS bT 
              [[s sP] [f fP]] 
              [[t tP] [g gP]] 
              [ [uS | [s3 s4]] cS ] 
              [ [uT | [t3 t4]] cT ]; 
       compute; reflexivity. 
Defined. 

*) 
Lemma correct_assert_not_is_left_product : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (ntT : brel_nontrivial T rT) 
        (nlS : bop_not_is_left S rS bS), 
          assert_product_not_is_left_left S T
             (p2c_nontrivial T rT ntT)
             (p2c_not_is_left S rS bS nlS)
          = 
          p2c_not_is_left (S * T) 
             (brel_product S T rS rT)
             (bop_product S T bS bT)
             (bop_product_not_is_left_left S T rS rT bS bT ntT nlS). 
Proof. intros S T rS rT bS bT [[s sP] negS] [ [t1 t2] PT]. 
       compute. reflexivity. 
Defined. 


Lemma correct_check_is_right_product : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (dS : bop_is_right_decidable S rS bS)
         (dT : bop_is_right_decidable T rT bT),
         check_is_right_product S T 
            (p2c_nontrivial S rS ntS) 
            (p2c_nontrivial T rT ntT) 
            (p2c_is_right_check S rS bS dS)
            (p2c_is_right_check T rT bT dT)
         = 
         p2c_is_right_check (S * T) 
            (brel_product S T rS rT) 
            (bop_product S T bS bT)
            (bop_product_is_right_decide S T rS rT bS bT ntS ntT dS dT). 
Proof. intros S T rS rT bS bT ntS ntT. 
       destruct ntS as [[s sP] [f fP]]. destruct ntT as [[t tP] [g gP]]. 
       intros [cS | [ [s3 s4] ncS]] [cT | [ [t3 t4] ncT]]; 
       compute; reflexivity. 
Defined. 

(*
Lemma correct_check_is_right_product_new : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (dS : bop_is_right_decidable_new S rS bS)
         (dT : bop_is_right_decidable_new T rT bT),
         check_is_right_product_new S T 
            (nontrivial_witness S (p2c_nontrivial S rS ntS))
            (nontrivial_witness T (p2c_nontrivial T rT ntT)) 
            (projT1 dS)
            (projT1 dT)
         = 
         projT1 (bop_product_is_right_decide_new S T rS rT bS bT ntS ntT dS dT). 
Proof. intros S T rS rT bS bT 
              [[s sP] [f fP]] 
              [[t tP] [g gP]] 
              [ [uS | [s3 s4]] cS ] 
              [ [uT | [t3 t4]] cT ]; 
       compute; reflexivity. 
Defined. 
*) 

Lemma correct_assert_not_is_right_product : 
      ∀ (S T : Type) 
        (rS : brel S) 
        (rT : brel T) 
        (bS : binary_op S) 
        (bT : binary_op T) 
        (ntS : brel_nontrivial S rS) 
        (nrT : bop_not_is_right T rT bT), 
          assert_product_not_is_right_right S T
             (p2c_nontrivial S rS ntS)
             (p2c_not_is_right T rT bT nrT)
          = 
          p2c_not_is_right (S * T) 
             (brel_product S T rS rT)
             (bop_product S T bS bT)
             (bop_product_not_is_right_right S T rS rT bS bT ntS nrT). 
Proof. intros S T rS rT bS bT [[s sP] negS] [ [t1 t2] PT]. 
       compute. reflexivity. 
Defined. 




Lemma correct_check_idempotent_product : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (dS : bop_idempotent_decidable S rS bS)
         (dT : bop_idempotent_decidable T rT bT),
         check_idempotent_product S T 
            (p2c_nontrivial S rS ntS) 
            (p2c_nontrivial T rT ntT) 
            (p2c_idempotent_check S rS bS dS)
            (p2c_idempotent_check T rT bT dT)
         = 
         p2c_idempotent_check (S * T) 
            (brel_product S T rS rT) 
            (bop_product S T bS bT)
            (bop_product_idempotent_decide S T rS rT bS bT ntS ntT dS dT). 
Proof. intros S T rS rT bS bT ntS ntT. 
       destruct ntS as [[s sP] [f fP]]. destruct ntT as [[t tP] [g gP]]. 
       intros [cS | [s3 niS]] [cT | [t3 niT]]; 
       compute; reflexivity. 
Defined. 

(*
Lemma correct_check_idempotent_product_new : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (dS : bop_idempotent_decidable_new S rS bS)
         (dT : bop_idempotent_decidable_new T rT bT),
         check_idempotent_product_new S T 
            (nontrivial_witness S (p2c_nontrivial S rS ntS)) 
            (nontrivial_witness T (p2c_nontrivial T rT ntT))
            (projT1 dS)
            (projT1 dT)
         = 
         projT1 (bop_product_idempotent_decide_new S T rS rT bS bT ntS ntT dS dT). 
Proof. intros S T rS rT bS bT 
              [[s sP] [f fP]] 
              [[t tP] [g gP]] 
              [ [uS | s3] cS ] 
              [ [uT | t3] cT ]; 
       compute; reflexivity. 
Defined. 
*) 

Lemma correct_check_exists_id_product : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (dS : bop_exists_id_decidable S rS bS)
         (dT : bop_exists_id_decidable T rT bT),
         check_exists_id_product S T
           (p2c_exists_id_check S rS bS dS)
           (p2c_exists_id_check T rT bT dT)
         =
         p2c_exists_id_check (S * T) 
            (brel_product S T rS rT)
            (bop_product S T bS bT)
            (bop_product_exists_id_decide S T rS rT bS bT dS dT).
Proof. intros S T rS rT bS bT [[s sP] | nS ] [[t tP] | nT ];
       compute; reflexivity. 
Defined. 

(*
Lemma correct_check_exists_id_product_new : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (dS : bop_exists_id_decidable_new S rS bS)
         (dT : bop_exists_id_decidable_new T rT bT),
         check_exists_id_product_new S T (projT1 dS) (projT1 dT)
         =
         projT1 (bop_product_exists_id_decide_new S T rS rT bS bT dS dT).
Proof. intros S T rS rT bS bT 
              [ [s | uS] cS ] 
              [ [t | uT] cT ]; 
       compute; reflexivity. 
Defined. 
*) 

Lemma correct_check_exists_ann_product : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (dS : bop_exists_ann_decidable S rS bS)
         (dT : bop_exists_ann_decidable T rT bT),
         check_exists_ann_product S T
           (p2c_exists_ann_check S rS bS dS)
           (p2c_exists_ann_check T rT bT dT)
         =
         p2c_exists_ann_check (S * T) 
            (brel_product S T rS rT)
            (bop_product S T bS bT)
            (bop_product_exists_ann_decide S T rS rT bS bT dS dT).
Proof. intros S T rS rT bS bT [[s sP] | nS ] [[t tP] | nT ];
       compute; reflexivity. 
Defined. 


(*
Lemma correct_check_exists_ann_product_new : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (dS : bop_exists_ann_decidable_new S rS bS)
         (dT : bop_exists_ann_decidable_new T rT bT),
         check_exists_ann_product_new S T (projT1 dS) (projT1 dT)
         =
         projT1 (bop_product_exists_ann_decide_new S T rS rT bS bT dS dT).
Proof. intros S T rS rT bS bT 
              [ [s | uS] cS ] 
              [ [t | uT] cT ]; 
       compute; reflexivity. 
Defined. 
*) 

Lemma correct_check_selective_product : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (symS : brel_symmetric S rS) 
         (symT : brel_symmetric T rT) 
         (transS : brel_transitive S rS) 
         (transT : brel_transitive T rT) 
         (dlS : bop_is_left_decidable S rS bS)
         (dlT : bop_is_left_decidable T rT bT)
         (drS : bop_is_right_decidable S rS bS)
         (drT : bop_is_right_decidable T rT bT),
         p2c_selective_check (S * T) 
            (brel_product S T rS rT) 
            (bop_product S T bS bT)
            (bop_product_selective_decide S T rS rT bS bT ntS ntT symS symT transS transT dlS dlT drS drT)
         = 
         check_selective_product S T 
            (p2c_nontrivial S rS ntS) 
            (p2c_nontrivial T rT ntT) 
            (p2c_is_left_check S rS bS dlS)
            (p2c_is_left_check T rT bT dlT)
            (p2c_is_right_check S rS bS drS)
            (p2c_is_right_check T rT bT drT). 
Proof. intros S T rS rT bS bT ntS ntT symS symT transS transT. 
       assert(ntS0 := ntS).        
       assert(ntT0 := ntT). 
       destruct ntS as [[s sP] [f fP]]. destruct ntT as [[t tP] [g gP]]. 
       intros [ilS | [ [s3 s4] nilS]] [ilT | [ [t3 t4] nilT]]
              [irS | [ [s5 s6] nirS]] [irT | [ [t5 t6] nirT]]; 
          compute; auto. 
          assert (F := bop_not_left_or_not_right S rS bS ntS0 symS transS ilS irS). 
             elim F. 
          assert (F := bop_not_left_or_not_right T rT bT ntT0 symT transT ilT irT). 
             elim F. 
Defined. 

(*
Lemma correct_check_selective_product_new : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (symS : brel_symmetric S rS) 
         (symT : brel_symmetric T rT) 
         (transS : brel_transitive S rS) 
         (transT : brel_transitive T rT) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (dlS : bop_is_left_decidable_new S rS bS)
         (dlT : bop_is_left_decidable_new T rT bT)
         (drS : bop_is_right_decidable_new S rS bS)
         (drT : bop_is_right_decidable_new T rT bT),
         projT1 (bop_product_selective_decide_new S T rS rT bS bT ntS ntT symS symT transS transT dlS dlT drS drT)
         = 
         check_selective_product_new S T 
            (nontrivial_witness S (p2c_nontrivial S rS ntS)) 
            (nontrivial_witness T (p2c_nontrivial T rT ntT)) 
            (projT1 dlS) (projT1 dlT) (projT1 drS)  (projT1  drT). 
Proof. intros S T rS rT bS bT symS symT transS transT
              [[s0 sP] [f fP]] 
              [[t0 tP] [g gP]] 
              [ [u1 | [s1 s2]] ldS ] 
              [ [u2 | [t1 t2]] ldT ]
              [ [u3 | [s3 s4]] rdS ] 
              [ [u4 | [t3 t4]] rdT ];
       compute; reflexivity. 
Defined. 
*) 

(*
Lemma correct_check_selective_product_commutative_case : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (symS : brel_symmetric S rS) 
         (symT : brel_symmetric T rT) 
         (transS : brel_transitive S rS) 
         (transT : brel_transitive T rT) 
         (commS : bop_commutative S rS bS)
         (commT : bop_commutative T rT bT), 
         p2c_selective_check (S * T) 
            (brel_product S T rS rT) 
            (bop_product S T bS bT)
            (bop_product_selective_decide_commutative_case 
               S T rS rT bS bT ntS ntT symS symT transS transT commS commT)
         = 
         check_selective_product_commutative_case S T rS rT bS bT
            (p2c_nontrivial S rS ntS) (p2c_nontrivial T rT ntT). 
Proof. intros S T rS rT bS bT ntS ntT symS symT transS transT commS commT.  
       destruct ntS as [[s sP] [f fP]]. destruct ntT as [[t tP] [g gP]]. 
       unfold p2c_nontrivial. 
       unfold p2c_witness, p2c_negate. 
       unfold brel_nontrivial_witness. 
       unfold brel_nontrivial_negate. 
       unfold projT1. 
       unfold check_selective_product_commutative_case. 
       unfold check_selective_product. 
       unfold certify_nontrivial_witness. 
       unfold nontrivial_witness. 
        unfold certify_nontrivial_witness. 
       unfold get_witness. 
       unfold nontrivial_negate. 
       unfold certify_nontrivial_negate.        
       unfold get_negate. 

       unfold bop_product_selective_decide_commutative_case. 
       unfold bop_product_selective_decide. 
       unfold p2c_selective_check. 

       unfold bop_commutative_implies_not_is_left . 

       unfold bop_product_not_selective. 



Defined. 
*) 
            


Lemma correct_check_left_cancel_product : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (refS : brel_reflexive S rS) 
         (refT : brel_reflexive T rT)
         (dS : bop_left_cancellative_decidable S rS bS)
         (dT : bop_left_cancellative_decidable T rT bT),
         p2c_left_cancel_check (S * T) 
            (brel_product S T rS rT) 
            (bop_product S T bS bT)
            (bop_product_left_cancellative_decide S T rS rT bS bT ntS ntT refS refT dS dT)
         = 
         check_left_cancellative_product S T 
            (p2c_nontrivial S rS ntS) 
            (p2c_nontrivial T rT ntT) 
            (p2c_left_cancel_check S rS bS dS)
            (p2c_left_cancel_check T rT bT dT). 
Proof. intros S T rS rT bS bT ntS ntT refS refT. 
       destruct ntS as [[s sP] [f fP]]. destruct ntT as [[t tP] [g gP]]. 
       intros [cS | [ [s3 [s4 s5]] [ncSL ncSR]] ] [cT | [ [t3 [t4 t5]] [ncTL ncTR] ] ]; 
       compute; reflexivity. 
Defined. 

(*
Lemma correct_check_left_cancel_product_new : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (refS : brel_reflexive S rS) 
         (refT : brel_reflexive T rT)
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (dS : bop_left_cancellative_decidable_new S rS bS)
         (dT : bop_left_cancellative_decidable_new T rT bT),
         projT1 (bop_product_left_cancellative_decide_new S T rS rT bS bT ntS ntT refS refT dS dT)
         = 
         check_left_cancellative_product_new S T 
            (nontrivial_witness S (p2c_nontrivial S rS ntS)) 
            (nontrivial_witness T (p2c_nontrivial T rT ntT))
            (projT1 dS)
            (projT1 dT).
Proof. intros S T rS rT bS bT refS refT 
              [[s sP] [f fP]] 
              [[t tP] [g gP]] 
              [ [uS | [s1 [s2 s3]]] cS ] 
              [ [uT | [t1 [t2 t3]]] cT ]; 
       compute; reflexivity. 
Defined. 
 
*) 

Lemma correct_check_right_cancel_product : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (refS : brel_reflexive S rS) 
         (refT : brel_reflexive T rT)
         (dS : bop_right_cancellative_decidable S rS bS)
         (dT : bop_right_cancellative_decidable T rT bT),
         p2c_right_cancel_check (S * T) 
            (brel_product S T rS rT) 
            (bop_product S T bS bT)
            (bop_product_right_cancellative_decide S T rS rT bS bT ntS ntT refS refT dS dT)
         = 
         check_right_cancellative_product S T 
            (p2c_nontrivial S rS ntS) 
            (p2c_nontrivial T rT ntT) 
            (p2c_right_cancel_check S rS bS dS)
            (p2c_right_cancel_check T rT bT dT). 
Proof. intros S T rS rT bS bT ntS ntT refS refT. 
       destruct ntS as [[s sP] [f fP]]. destruct ntT as [[t tP] [g gP]]. 
       intros [cS | [ [s3 [s4 s5]] [ncSL ncSR]] ] [cT | [ [t3 [t4 t5]] [ncTL ncTR] ] ]; 
       compute; reflexivity. 
Defined. 

(*
Lemma correct_check_right_cancel_product_new : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (refS : brel_reflexive S rS) 
         (refT : brel_reflexive T rT)
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (dS : bop_right_cancellative_decidable_new S rS bS)
         (dT : bop_right_cancellative_decidable_new T rT bT),
         projT1 (bop_product_right_cancellative_decide_new S T rS rT bS bT ntS ntT refS refT dS dT)
         = 
         check_right_cancellative_product_new S T 
            (nontrivial_witness S (p2c_nontrivial S rS ntS)) 
            (nontrivial_witness T (p2c_nontrivial T rT ntT))
            (projT1 dS)
            (projT1 dT).
Proof. intros S T rS rT bS bT refS refT 
              [[s sP] [f fP]] 
              [[t tP] [g gP]] 
              [ [uS | [s1 [s2 s3]]] cS ] 
              [ [uT | [t1 [t2 t3]]] cT ]; 
       compute; reflexivity. 
Defined. 
*) 


Lemma correct_check_left_constant_product : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (dS : bop_left_constant_decidable S rS bS)
         (dT : bop_left_constant_decidable T rT bT),
         p2c_left_constant_check (S * T) 
            (brel_product S T rS rT) 
            (bop_product S T bS bT)
            (bop_product_left_constant_decide S T rS rT bS bT ntS ntT dS dT)
         = 
         check_left_constant_product S T 
            (p2c_nontrivial S rS ntS) 
            (p2c_nontrivial T rT ntT) 
            (p2c_left_constant_check S rS bS dS)
            (p2c_left_constant_check T rT bT dT).
Proof. intros S T rS rT bS bT ntS ntT. 
       destruct ntS as [[s sP] [f fP]]. destruct ntT as [[t tP] [g gP]]. 
       intros [cS | [ [s3 [s4 s5]] ncS] ] [cT | [ [t3 [t4 t5]] ncT] ]; 
       compute; reflexivity. 
Defined. 

(*
Lemma correct_check_left_constant_product_new : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (dS : bop_left_constant_decidable_new S rS bS)
         (dT : bop_left_constant_decidable_new T rT bT),
         projT1 (bop_product_left_constant_decide_new S T rS rT bS bT ntS ntT dS dT)
         = 
         check_left_constant_product_new S T 
            (nontrivial_witness S (p2c_nontrivial S rS ntS)) 
            (nontrivial_witness T( p2c_nontrivial T rT ntT))
            (projT1 dS)
            (projT1 dT).
Proof. intros S T rS rT bS bT
              [[s sP] [f fP]] 
              [[t tP] [g gP]] 
              [ [uS | [s1 [s2 s3]]] cS ] 
              [ [uT | [t1 [t2 t3]]] cT ]; 
       compute; reflexivity. 
Defined. 
*) 

Lemma correct_check_right_constant_product : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (dS : bop_right_constant_decidable S rS bS)
         (dT : bop_right_constant_decidable T rT bT),
         p2c_right_constant_check (S * T) 
            (brel_product S T rS rT) 
            (bop_product S T bS bT)
            (bop_product_right_constant_decide S T rS rT bS bT ntS ntT dS dT)
         = 
         check_right_constant_product S T 
            (p2c_nontrivial S rS ntS) 
            (p2c_nontrivial T rT ntT) 
            (p2c_right_constant_check S rS bS dS)
            (p2c_right_constant_check T rT bT dT).
Proof. intros S T rS rT bS bT ntS ntT. 
       destruct ntS as [[s sP] [f fP]]. destruct ntT as [[t tP] [g gP]]. 
       intros [cS | [ [s3 [s4 s5]] ncS] ] [cT | [ [t3 [t4 t5]] ncT] ]; 
       compute; reflexivity. 
Defined. 


(*

Lemma correct_check_right_constant_product_new : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (dS : bop_right_constant_decidable_new S rS bS)
         (dT : bop_right_constant_decidable_new T rT bT),
         projT1 (bop_product_right_constant_decide_new S T rS rT bS bT ntS ntT dS dT)
         = 
         check_right_constant_product_new S T 
            (nontrivial_witness S (p2c_nontrivial S rS ntS)) 
            (nontrivial_witness T( p2c_nontrivial T rT ntT))
            (projT1 dS)
            (projT1 dT).
Proof. intros S T rS rT bS bT
              [[s sP] [f fP]] 
              [[t tP] [g gP]] 
              [ [uS | [s1 [s2 s3]]] cS ] 
              [ [uT | [t1 [t2 t3]]] cT ]; 
       compute; reflexivity. 
Defined. 

*) 

Lemma correct_check_anti_left_product : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (dS : bop_anti_left_decidable S rS bS)
         (dT : bop_anti_left_decidable T rT bT),
         p2c_anti_left_check (S * T) 
            (brel_product S T rS rT) 
            (bop_product S T bS bT)
            (bop_product_anti_left_decide S T rS rT bS bT dS dT)
         = 
         check_anti_left_product S T 
            (p2c_anti_left_check S rS bS dS)
            (p2c_anti_left_check T rT bT dT).
Proof. intros S T rS rT bS bT [cS | [ [s3 s4] ncS] ] [cT | [ [t3 t4] ncT] ]; 
       compute; reflexivity. 
Defined. 

(*

Lemma correct_check_anti_left_product_new : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (dS : bop_anti_left_decidable_new S rS bS)
         (dT : bop_anti_left_decidable_new T rT bT),
         projT1 (bop_product_anti_left_decide_new S T rS rT bS bT dS dT)
         = 
         check_anti_left_product_new S T (projT1 dS) (projT1 dT). 
Proof. intros S T rS rT bS bT
              [ [uS | [s2 s3]] cS ] 
              [ [uT | [t2 t3]] cT ]; 
       compute; reflexivity. 
Defined. 
*) 

Lemma correct_check_anti_right_product : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (dS : bop_anti_right_decidable S rS bS)
         (dT : bop_anti_right_decidable T rT bT),
         p2c_anti_right_check (S * T) 
            (brel_product S T rS rT) 
            (bop_product S T bS bT)
            (bop_product_anti_right_decide S T rS rT bS bT dS dT)
         = 
         check_anti_right_product S T 
            (p2c_anti_right_check S rS bS dS)
            (p2c_anti_right_check T rT bT dT).
Proof. intros S T rS rT bS bT [cS | [ [s3 s4] ncS] ] [cT | [ [t3 t4] ncT] ]; 
       compute; reflexivity. 
Defined. 

(*
Lemma correct_check_anti_right_product_new : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (dS : bop_anti_right_decidable_new S rS bS)
         (dT : bop_anti_right_decidable_new T rT bT),
         projT1 (bop_product_anti_right_decide_new S T rS rT bS bT dS dT)
         = 
         check_anti_right_product_new S T (projT1 dS) (projT1 dT). 
Proof. intros S T rS rT bS bT
              [ [uS | [s2 s3]] cS ] 
              [ [uT | [t2 t3]] cT ]; 
       compute; reflexivity. 
Defined. 
*) 


(* bop llex *) 

Lemma correct_check_commutative_llex : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (congS : brel_congruence S rS rS)
         (refS : brel_reflexive S rS)
         (symS : brel_symmetric S rS)
         (transS : brel_transitive S rS)
         (refT : brel_reflexive T rT)
         (selS : bop_selective S rS bS) 
         (commS : bop_commutative S rS bS)
         (dT : bop_commutative_decidable T rT bT),
         p2c_commutative_check (S * T) 
            (brel_product S T rS rT) 
            (bop_llex S T rS bS bT)
            (bop_llex_commutative_decide S T rS rT bS bT 
                 (brel_nontrivial_witness S rS ntS) 
                 (brel_nontrivial_witness T rT ntT) 
                 congS refS symS transS refT selS 
                 (inl _ commS) 
                 dT
            )
         = 
         check_commutative_llex S T 
            (p2c_nontrivial S rS ntS) 
            (p2c_commutative_check T rT bT dT). 
Proof. intros S T rS rT bS bT ntS ntT congS refS symS transS refT selS. 
       destruct ntS as [[s sP] [f fP]]. destruct ntT as [[t tP] [g gP]]. 
       intros commS [cT | [ [t3 t4] ncT]]; 
       compute; reflexivity. 
Defined. 


Lemma correct_check_idempotent_llex : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (ntT : brel_nontrivial T rT)
         (refS : brel_reflexive S rS)
         (refT : brel_reflexive T rT)
         (selS : bop_selective S rS bS)
         (dT : bop_idempotent_decidable T rT bT),
         p2c_idempotent_check (S * T) 
            (brel_product S T rS rT) 
            (bop_llex S T rS bS bT)
            (bop_llex_idempotent_decide S T rS rT bS bT 
                 (brel_nontrivial_witness S rS ntS) 
                 (brel_nontrivial_witness T rT ntT) 
                 refS refT 
                 (inl _ (bop_selective_implies_idempotent S rS bS selS)) 
                 dT
            )
         = 
         check_idempotent_llex S T 
            (p2c_nontrivial S rS ntS) 
            (p2c_idempotent_check T rT bT dT).
Proof. intros S T rS rT bS bT ntS ntT refS refT selS. 
       destruct ntS as [[s sP] [f fP]]. destruct ntT as [[t tP] [g gP]]. 
       intros [cT | [t3 niT]]; 
       compute; reflexivity. 
Defined. 

Lemma correct_check_exists_id_llex : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (refS : brel_reflexive S rS)
         (symS : brel_symmetric S rS)
         (transS : brel_transitive S rS)
         (commS : bop_commutative S rS bS)
         (refT : brel_reflexive T rT)
         (dS : bop_exists_id_decidable S rS bS)
         (dT : bop_exists_id_decidable T rT bT),
         p2c_exists_id_check (S * T) 
            (brel_product S T rS rT)
            (bop_llex S T rS bS bT)
            (bop_llex_exists_id_decide S T rS rT bS bT refS symS transS refT commS dS dT)
         =
         check_exists_id_llex S T
           (p2c_exists_id_check S rS bS dS)
           (p2c_exists_id_check T rT bT dT). 
Proof. intros S T rS rT bS bT refS symS transS refT commS [[s sP] | nS ] [[t tP] | nT ];
       compute; reflexivity. 
Defined. 


Lemma correct_check_exists_ann_llex : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (refS : brel_reflexive S rS)
         (symS : brel_symmetric S rS)
         (transS : brel_transitive S rS)
         (commS : bop_commutative S rS bS)
         (refT : brel_reflexive T rT)
         (dS : bop_exists_ann_decidable S rS bS)
         (dT : bop_exists_ann_decidable T rT bT),

         p2c_exists_ann_check (S * T) 
            (brel_product S T rS rT)
            (bop_llex S T rS bS bT)
            (bop_llex_exists_ann_decide S T rS rT bS bT refS symS transS refT commS dS dT)
         =
         check_exists_ann_llex S T
           (p2c_exists_ann_check S rS bS dS)
           (p2c_exists_ann_check T rT bT dT). 
Proof. intros S T rS rT bS bT refS symS transS refT commS [[s sP] | nS ] [[t tP] | nT ];
       compute; reflexivity. 
Defined. 

Lemma correct_check_selective_llex : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS)
         (refS : brel_reflexive S rS)
         (symS : brel_symmetric S rS) 
         (transS : brel_transitive S rS) 
         (congS : brel_congruence S rS rS) 
         (b_congS : bop_congruence S rS bS) 
         (commS : bop_commutative S rS bS)
         (selS : bop_selective S rS bS)
         (refT : brel_reflexive T rT)
         (dT : bop_selective_decidable T rT bT),

         p2c_selective_check (S * T) 
            (brel_product S T rS rT) 
            (bop_llex S T rS bS bT)
            (bop_llex_selective_decide S T rS rT bS bT 
              (brel_nontrivial_witness S rS ntS)  
              refS symS transS congS b_congS commS selS refT dT)
         = 
         check_selective_llex S T 
            (p2c_nontrivial S rS ntS) 
            (p2c_selective_check T rT bT dT). 
Proof. intros S T rS rT bS bT [[s Ps] Ns] refS symS transS congS b_congS commS selS refT. 
       intros [selT | [ [t1 t2] P]]; compute; reflexivity. 
Defined. 



Lemma correct_not_left_cancellative_llex : ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S)
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS) 
         (ntT : brel_nontrivial T rT) 
         (refS : brel_reflexive S rS)
         (symS : brel_symmetric S rS)
         (transS : brel_transitive S rS)
         (congS : bop_congruence S rS bS)
         (selS : bop_selective S rS bS)
         (commS : bop_commutative S rS bS)
         (refT : brel_reflexive T rT),
   projT1 (bop_llex_not_left_cancellative_v2 S T rS rT bS bT ntS ntT 
              refS symS transS congS selS commS refT)
   = 
   cef.cef_bop_llex_not_cancellative S T rS bS
      (nontrivial_witness S (p2c_nontrivial S rS ntS))
      (nontrivial_negate S (p2c_nontrivial S rS ntS))
      (nontrivial_witness T (p2c_nontrivial T rT ntT))
      (nontrivial_negate T (p2c_nontrivial T rT ntT)).
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] refS symS transS congS selS commS refT.
       compute. reflexivity. 
Qed.       

Lemma correct_not_right_cancellative_llex : ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S)
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS) 
         (ntT : brel_nontrivial T rT) 
         (refS : brel_reflexive S rS)
         (symS : brel_symmetric S rS)
         (transS : brel_transitive S rS)
         (congS : bop_congruence S rS bS)
         (selS : bop_selective S rS bS)
         (commS : bop_commutative S rS bS)
         (refT : brel_reflexive T rT),
   projT1 (bop_llex_not_right_cancellative S T rS rT bS bT ntS ntT 
              refS symS transS congS selS commS refT)
   = 
   cef.cef_bop_llex_not_cancellative S T rS bS
      (nontrivial_witness S (p2c_nontrivial S rS ntS))
      (nontrivial_negate S (p2c_nontrivial S rS ntS))
      (nontrivial_witness T (p2c_nontrivial T rT ntT))
      (nontrivial_negate T (p2c_nontrivial T rT ntT)). 
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] refS symS transS congS selS commS refT.
       compute. reflexivity. 
Qed.       



Lemma correct_not_left_constant_llex : ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S)
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS) 
         (ntT : brel_nontrivial T rT) 
         (refS : brel_reflexive S rS)
         (symS : brel_symmetric S rS)
         (transS : brel_transitive S rS)
         (congS : bop_congruence S rS bS)
         (selS : bop_selective S rS bS)
         (commS : bop_commutative S rS bS)
         (refT : brel_reflexive T rT),
   projT1 (bop_llex_not_left_constant S T rS rT bS bT ntS ntT 
              refS symS transS congS selS commS refT)
   = 
   cef.cef_bop_llex_not_constant S T rS bS
      (nontrivial_witness S (p2c_nontrivial S rS ntS))
      (nontrivial_negate S (p2c_nontrivial S rS ntS))
      (nontrivial_witness T (p2c_nontrivial T rT ntT))
      (nontrivial_negate T (p2c_nontrivial T rT ntT)). 
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] refS symS transS congS selS commS refT.
       compute. reflexivity. 
Qed.       



Lemma correct_not_right_constant_llex : ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S)
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS) 
         (ntT : brel_nontrivial T rT) 
         (refS : brel_reflexive S rS)
         (symS : brel_symmetric S rS)
         (transS : brel_transitive S rS)
         (congS : bop_congruence S rS bS)
         (selS : bop_selective S rS bS)
         (commS : bop_commutative S rS bS)
         (refT : brel_reflexive T rT),
   projT1 (bop_llex_not_right_constant S T rS rT bS bT ntS ntT 
              refS symS transS congS selS commS refT)
   = 
   cef.cef_bop_llex_not_constant S T rS bS
      (nontrivial_witness S (p2c_nontrivial S rS ntS))
      (nontrivial_negate S (p2c_nontrivial S rS ntS))
      (nontrivial_witness T (p2c_nontrivial T rT ntT))
      (nontrivial_negate T (p2c_nontrivial T rT ntT)). 
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] refS symS transS congS selS commS refT.
       compute. reflexivity. 
Qed.       


Lemma correct_not_anti_left_llex : ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S)
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS) 
         (ntT : brel_nontrivial T rT) 
         (symS : brel_symmetric S rS)
         (transS : brel_transitive S rS)
         (selS : bop_selective S rS bS)
         (commS : bop_commutative S rS bS)
         (refT : brel_reflexive T rT),
   projT1 (bop_llex_not_anti_left S T rS rT bS bT ntS (brel_nontrivial_witness T rT ntT)
              symS transS selS commS refT)
   = 
   cef.cef_bop_llex_not_anti_left S T rS bS
      (nontrivial_witness S (p2c_nontrivial S rS ntS))
      (nontrivial_negate S (p2c_nontrivial S rS ntS))
      (nontrivial_witness T (p2c_nontrivial T rT ntT)).
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] symS transS selS commS refT.
       compute. reflexivity. 
Qed.       


Lemma correct_not_anti_right_llex : ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S)
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS) 
         (ntT : brel_nontrivial T rT) 
         (symS : brel_symmetric S rS)
         (transS : brel_transitive S rS)
         (selS : bop_selective S rS bS)
         (commS : bop_commutative S rS bS)
         (refT : brel_reflexive T rT),
   projT1 (bop_llex_not_anti_right S T rS rT bS bT ntS (brel_nontrivial_witness T rT ntT)
              symS transS selS commS refT)
   = 
   cef.cef_bop_llex_not_anti_right S T rS bS
      (nontrivial_witness S (p2c_nontrivial S rS ntS))
      (nontrivial_negate S (p2c_nontrivial S rS ntS))
      (nontrivial_witness T (p2c_nontrivial T rT ntT)).
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] symS transS selS commS refT.
       compute. reflexivity. 
Qed.       



Lemma correct_not_is_left_llex : ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S)
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS) 
         (ntT : brel_nontrivial T rT) 
         (symS : brel_symmetric S rS)
         (transS : brel_transitive S rS)
         (selS : bop_selective S rS bS)
         (commS : bop_commutative S rS bS),
  projT1 (bop_llex_not_is_left S T rS rT bS bT ntS (brel_nontrivial_witness T rT ntT)
              transS symS commS selS)
   = 
   cef.cef_bop_llex_not_is_left S T rS bS
      (nontrivial_witness S (p2c_nontrivial S rS ntS))
      (nontrivial_negate S (p2c_nontrivial S rS ntS))
      (nontrivial_witness T (p2c_nontrivial T rT ntT)).
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] symS transS selS commS.
       compute. reflexivity. 
Qed.       


Lemma correct_not_is_right_llex : ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S)
         (bT : binary_op T) 
         (ntS : brel_nontrivial S rS) 
         (ntT : brel_nontrivial T rT) 
         (symS : brel_symmetric S rS)
         (transS : brel_transitive S rS)
         (selS : bop_selective S rS bS)
         (commS : bop_commutative S rS bS),
  projT1 (bop_llex_not_is_right S T rS rT bS bT ntS (brel_nontrivial_witness T rT ntT)
              transS symS commS selS)
   = 
   cef.cef_bop_llex_not_is_right S T rS bS
      (nontrivial_witness S (p2c_nontrivial S rS ntS))
      (nontrivial_negate S (p2c_nontrivial S rS ntS))
      (nontrivial_witness T (p2c_nontrivial T rT ntT)).
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] symS transS selS commS.
       compute. reflexivity. 
Qed.     




(* left sum *) 


Lemma correct_check_commutative_left_sum : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (refS : brel_reflexive S rS)
         (dS : bop_commutative_decidable S rS bS)
         (dT : bop_commutative_decidable T rT bT),
         check_commutative_sum S T 
            (p2c_commutative_check S rS bS dS)
            (p2c_commutative_check T rT bT dT)
         = 
         p2c_commutative_check (S + T) 
            (brel_sum S T rS rT) 
            (bop_left_sum S T bS bT)
            (bop_left_sum_commutative_decide S T rS rT bS bT refS dS dT). 
Proof. intros S T rS rT bS bT refS [cS | [ [s3 s4] ncS]] [cT | [ [t3 t4] ncT]]; 
       compute; reflexivity. 
Defined. 


Lemma correct_check_idempotent_left_sum : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (dS : bop_idempotent_decidable S rS bS)
         (dT : bop_idempotent_decidable T rT bT),
         check_idempotent_sum S T 
            (p2c_idempotent_check S rS bS dS)
            (p2c_idempotent_check T rT bT dT)
         = 
         p2c_idempotent_check (S + T) 
            (brel_sum S T rS rT) 
            (bop_left_sum S T bS bT)
            (bop_left_sum_idempotent_decide S T rS rT bS bT dS dT). 
Proof. intros S T rS rT bS bT [cS | [s4 ncS]] [cT | [t4 ncT]]; 
       compute; reflexivity. 
Defined. 

Lemma correct_check_selective_left_sum : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (refS : brel_reflexive S rS)
         (dS : bop_selective_decidable S rS bS)
         (dT : bop_selective_decidable T rT bT),
         check_selective_sum S T 
            (p2c_selective_check S rS bS dS)
            (p2c_selective_check T rT bT dT)
         = 
         p2c_selective_check (S + T) 
            (brel_sum S T rS rT) 
            (bop_left_sum S T bS bT)
            (bop_left_sum_selective_decide S T rS rT bS bT refS dS dT). 
Proof. intros S T rS rT bS bT refS [cS | [ [s3 s4] ncS]] [cT | [ [t3 t4] ncT]]; 
       compute; reflexivity. 
Defined. 

Lemma correct_check_exists_id_left_sum : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (refS : brel_reflexive S rS)
         (ntT : brel_nontrivial T rT)
         (dT : bop_exists_id_decidable T rT bT),
         check_exists_id_left_sum S T
           (p2c_exists_id_check T rT bT dT)
         =
         p2c_exists_id_check (S + T) 
            (brel_sum S T rS rT)
            (bop_left_sum S T bS bT)
            (bop_left_sum_exists_id_decide S T rS rT bS bT ntT refS dT).
Proof. intros S T rS rT bS bT refS ntT [[t tP] | nT ];
       compute; reflexivity. 
Defined. 

Lemma correct_check_exists_ann_left_sum : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (refS : brel_reflexive S rS)
         (ntS : brel_nontrivial S rS)
         (dS : bop_exists_ann_decidable S rS bS), 
         check_exists_ann_left_sum S T
           (p2c_exists_ann_check S rS bS dS)
         =
         p2c_exists_ann_check (S + T) 
            (brel_sum S T rS rT)
            (bop_left_sum S T bS bT)
            (bop_left_sum_exists_ann_decide S T rS rT bS bT ntS refS dS).
Proof. intros S T rS rT bS bT refS ntS [[s sP] | nS ];
       compute; reflexivity. 
Defined. 

(* right sum *) 

Lemma correct_check_commutative_right_sum : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (refT : brel_reflexive T rT)
         (dS : bop_commutative_decidable S rS bS)
         (dT : bop_commutative_decidable T rT bT),
         check_commutative_sum S T 
            (p2c_commutative_check S rS bS dS)
            (p2c_commutative_check T rT bT dT)
         = 
         p2c_commutative_check (S + T) 
            (brel_sum S T rS rT) 
            (bop_right_sum S T bS bT)
            (bop_right_sum_commutative_decide S T rS rT bS bT refT dS dT). 
Proof. intros S T rS rT bS bT refS [cS | [ [s3 s4] ncS]] [cT | [ [t3 t4] ncT]]; 
       compute; reflexivity. 
Defined. 


Lemma correct_check_idempotent_right_sum : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (dS : bop_idempotent_decidable S rS bS)
         (dT : bop_idempotent_decidable T rT bT),
         check_idempotent_sum S T 
            (p2c_idempotent_check S rS bS dS)
            (p2c_idempotent_check T rT bT dT)
         = 
         p2c_idempotent_check (S + T) 
            (brel_sum S T rS rT) 
            (bop_right_sum S T bS bT)
            (bop_right_sum_idempotent_decide S T rS rT bS bT dS dT). 
Proof. intros S T rS rT bS bT [cS | [s4 ncS]] [cT | [t4 ncT]]; 
       compute; reflexivity. 
Defined. 

Lemma correct_check_selective_right_sum : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (refT : brel_reflexive T rT)
         (dS : bop_selective_decidable S rS bS)
         (dT : bop_selective_decidable T rT bT),
         check_selective_sum S T 
            (p2c_selective_check S rS bS dS)
            (p2c_selective_check T rT bT dT)
         = 
         p2c_selective_check (S + T) 
            (brel_sum S T rS rT) 
            (bop_right_sum S T bS bT)
            (bop_right_sum_selective_decide S T rS rT bS bT refT dS dT). 
Proof. intros S T rS rT bS bT refS [cS | [ [s3 s4] ncS]] [cT | [ [t3 t4] ncT]]; 
       compute; reflexivity. 
Defined. 

Lemma correct_check_exists_id_right_sum : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (refT : brel_reflexive T rT)
         (ntS : brel_nontrivial S rS)
         (dS : bop_exists_id_decidable S rS bS),
         check_exists_id_right_sum S T
           (p2c_exists_id_check S rS bS dS)
         =
         p2c_exists_id_check (S + T) 
            (brel_sum S T rS rT)
            (bop_right_sum S T bS bT)
            (bop_right_sum_exists_id_decide S T rS rT bS bT ntS refT dS).
Proof. intros S T rS rT bS bT refT ntT [[t tP] | nT ];
       compute; reflexivity. 
Defined. 

Lemma correct_check_exists_ann_right_sum : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (refT : brel_reflexive T rT)
         (ntT : brel_nontrivial T rT)
         (dT : bop_exists_ann_decidable T rT bT), 
         check_exists_ann_right_sum S T
           (p2c_exists_ann_check T rT bT dT)
         =
         p2c_exists_ann_check (S + T) 
            (brel_sum S T rS rT)
            (bop_right_sum S T bS bT)
            (bop_right_sum_exists_ann_decide S T rS rT bS bT ntT refT dT).
Proof. intros S T rS rT bS bT refT ntS [[s sP] | nS ];
       compute; reflexivity. 
Defined. 


(* NOTATION NOTATION NOTATION *) 


(* THIS IS IN check_correct.v   !!!!

   Need collection of lemmas of the form 

   CON_P_check_correct : 
   
   ∀ (q1 : Q1_decidable) (q2 : Q2_decidable) ... (qk : Qk_decidable), 
     
     p2c_P_check (CON_P_decide q1 q2 ... qk) 
     = 
     CON_P_check (p2C_Q1_check q1) (p2C_Q2_check q2) ... (p2C_Qk_check qk)

*) 



Lemma bop_add_id_commutative_check_correct :       
     ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) 
       (refS : brel_reflexive S r) (p_d : bop_commutative_decidable S r b), 

     p2c_commutative_check (with_constant S)
                         (brel_add_constant S r c) 
                         (bop_add_id S b c)
                         (bop_add_id_commutative_decide S r c b refS p_d)
     =                          
     bop_add_id_commutative_check S (p2c_commutative_check S r b p_d). 
Proof. intros S r b c refS [p | [ [s1 s2] np]]; compute; reflexivity. Qed. 


Lemma bop_add_id_selective_check_correct :       
     ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) 
       (refS : brel_reflexive S r) (p_d : bop_selective_decidable S r b), 

     p2c_selective_check (with_constant S)
                         (brel_add_constant S r c) 
                         (bop_add_id S b c)
                         (bop_add_id_selective_decide S r c b refS p_d)
     =                          
     bop_add_id_selective_check S (p2c_selective_check S r b p_d). 
Proof. intros S r b c refS [p | [ [s1 s2] np]]; compute; reflexivity. Qed. 

Lemma bop_add_id_idempotent_check_correct :       
     ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) 
       (p_d : bop_idempotent_decidable S r b), 

     p2c_idempotent_check (with_constant S)
                         (brel_add_constant S r c) 
                         (bop_add_id S b c)
                         (bop_add_id_idempotent_decide S r c b p_d)
     =                          
     bop_add_id_idempotent_check S (p2c_idempotent_check S r b p_d). 
Proof. intros S r b c [p | [s np] ]; compute; reflexivity. Qed. 



Lemma bop_add_id_left_cancellative_check_correct :       
     ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) 
       (symS : brel_symmetric S r) (q_d : bop_anti_left_decidable S r b) 
       (p_d : bop_left_cancellative_decidable S r b), 

     p2c_left_cancel_check (with_constant S) (brel_add_constant S r c) (bop_add_id S b c)
        (bop_add_id_left_cancellative_decide S r c b symS q_d p_d)
     =                          
     bop_add_id_left_cancellative_check S c 
        (p2c_anti_left_check S r b q_d)
        (p2c_left_cancel_check S r b p_d). 
Proof. intros S r b c symS  [ q | [[s1 s2] nq] ] [p | [ [s3 [s4 s5]] np] ]; 
       compute; reflexivity. 
Qed. 


Lemma bop_add_id_right_cancellative_check_correct :       
     ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) 
       (symS : brel_symmetric S r) (q_d : bop_anti_right_decidable S r b) 
       (p_d : bop_right_cancellative_decidable S r b), 

     p2c_right_cancel_check (with_constant S) (brel_add_constant S r c) (bop_add_id S b c)
        (bop_add_id_right_cancellative_decide S r c b symS q_d p_d)
     =                          
     bop_add_id_right_cancellative_check S c 
        (p2c_anti_right_check S r b q_d)
        (p2c_right_cancel_check S r b p_d). 
Proof. intros S r b c symS  [ q | [[s1 s2] nq] ] [p | [ [s3 [s4 s5]] np] ]; 
       compute; reflexivity. 
Qed. 


Lemma bop_add_id_exists_ann_check_correct :       
     ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) 
       (ntS : brel_nontrivial S r) (refS : brel_reflexive S r) 
       (p_d : bop_exists_ann_decidable S r b), 

     p2c_exists_ann_check (with_constant S) (brel_add_constant S r c) (bop_add_id S b c)
        (bop_add_id_exists_ann_decide S r c b ntS refS p_d)
     =                          
     bop_add_id_exists_ann_check S (p2c_exists_ann_check S r b p_d). 
Proof. intros S r b c ntS refS [ [a p] | np ]; compute; reflexivity. Qed. 


(* add ann *) 
Lemma bop_add_ann_commutative_check_correct :       
     ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) 
       (refS : brel_reflexive S r) (p_d : bop_commutative_decidable S r b), 

     p2c_commutative_check (with_constant S)
                         (brel_add_constant S r c) 
                         (bop_add_ann S b c)
                         (bop_add_ann_commutative_decide S r c b refS p_d)
     =                          
     bop_add_ann_commutative_check S (p2c_commutative_check S r b p_d). 
Proof. intros S r b c refS [p | [ [s1 s2] np]]; compute; reflexivity. Qed. 


Lemma bop_add_ann_selective_check_correct :       
     ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) 
       (refS : brel_reflexive S r) (p_d : bop_selective_decidable S r b), 

     p2c_selective_check (with_constant S)
                         (brel_add_constant S r c) 
                         (bop_add_ann S b c)
                         (bop_add_ann_selective_decide S r c b refS p_d)
     =                          
     bop_add_ann_selective_check S (p2c_selective_check S r b p_d). 
Proof. intros S r b c refS [p | [ [s1 s2] np]]; compute; reflexivity. Qed. 

Lemma bop_add_ann_idempotent_check_correct :       
     ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) 
       (p_d : bop_idempotent_decidable S r b), 

     p2c_idempotent_check (with_constant S)
                         (brel_add_constant S r c) 
                         (bop_add_ann S b c)
                         (bop_add_ann_idempotent_decide S r c b p_d)
     =                          
     bop_add_ann_idempotent_check S (p2c_idempotent_check S r b p_d). 
Proof. intros S r b c [p | [s np] ]; compute; reflexivity. Qed. 


Lemma bop_add_ann_exists_id_check_correct :       
     ∀ (S : Type) (r : brel S) (b : binary_op S) (c : cas_constant) 
       (ntS : brel_nontrivial S r) (refS : brel_reflexive S r) 
       (p_d : bop_exists_id_decidable S r b), 

     p2c_exists_id_check (with_constant S) (brel_add_constant S r c) (bop_add_ann S b c)
        (bop_add_ann_exists_id_decide S r c b ntS refS p_d)
     =                          
     bop_add_ann_exists_id_check S (p2c_exists_id_check S r b p_d). 
Proof. intros S r b c ntS refS [ [a p] | np ]; compute; reflexivity. Qed. 


(* product product *) 


Lemma bop_product_left_distributive_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (ntS : brel_nontrivial S rS)
    (ntT : brel_nontrivial T rT)
    (pS_d : bop_left_distributive_decidable S rS plusS timesS) 
    (pT_d : bop_left_distributive_decidable T rT plusT timesT), 
   bop_product_left_distributive_check S T
       (p2c_nontrivial S rS ntS)
       (p2c_nontrivial T rT ntT)
       (p2c_left_distributive S rS plusS timesS pS_d)
       (p2c_left_distributive T rT plusT timesT pT_d)
     = 
     p2c_left_distributive (S * T) 
        (brel_product S T rS rT)
        (bop_product S T plusS plusT)
        (bop_product S T timesS timesT)
        (bop_product_left_distributive_decide S T rS rT plusS timesS plusT timesT 
            ntS ntT pS_d pT_d).
Proof. intros S T rS rT plusS timesS plusT timesT [[s Ps] [f Pf]] [[t Pt] [g Pg]] 
       [ ldS | [ [s1 [s2 s3]] nldS]] 
       [ ldT | [ [t1 [t2 t3]] nldT]]; compute; reflexivity. 
Qed. 

Lemma bop_product_right_distributive_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (ntS : brel_nontrivial S rS)
    (ntT : brel_nontrivial T rT)
    (pS_d : bop_right_distributive_decidable S rS plusS timesS) 
    (pT_d : bop_right_distributive_decidable T rT plusT timesT), 
   bop_product_right_distributive_check S T
       (p2c_nontrivial S rS ntS)
       (p2c_nontrivial T rT ntT)
       (p2c_right_distributive S rS plusS timesS pS_d)
       (p2c_right_distributive T rT plusT timesT pT_d)
     = 
     p2c_right_distributive (S * T) 
        (brel_product S T rS rT)
        (bop_product S T plusS plusT)
        (bop_product S T timesS timesT)
        (bop_product_right_distributive_decide S T rS rT plusS timesS plusT timesT 
            ntS ntT pS_d pT_d).
Proof. intros S T rS rT plusS timesS plusT timesT [[s Ps] [f Pf]] [[t Pt] [g Pg]] 
       [ ldS | [ [s1 [s2 s3]] nldS]] 
       [ ldT | [ [t1 [t2 t3]] nldT]]; compute; reflexivity. 
Qed. 


Lemma bop_product_plus_id_is_times_ann_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (pS_d : bops_id_equals_ann_decidable S rS plusS timesS)
    (pT_d : bops_id_equals_ann_decidable T rT plusT timesT), 
   p2c_plus_id_equals_times_ann (S * T) 
      (brel_product S T rS rT)
      (bop_product S T plusS plusT)
      (bop_product S T timesS timesT)
      (bop_product_id_equals_ann_decide S T rS rT plusS timesS plusT timesT pS_d pT_d)
   = 
   bop_product_plus_id_is_times_ann_check S T
      (p2c_plus_id_equals_times_ann S rS plusS timesS pS_d)
      (p2c_plus_id_equals_times_ann T rT plusT timesT pT_d). 
Proof. intros S T rS rT plusS timesS plusT timesT 
       [ eqS | neqS] [eqT | neqT] ; compute; reflexivity. 
Qed. 


Lemma bop_product_times_id_equals_plus_ann_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (pS_d : bops_id_equals_ann_decidable S rS timesS plusS)
    (pT_d : bops_id_equals_ann_decidable T rT timesT plusT), 
   p2c_times_id_equals_plus_ann (S * T) 
      (brel_product S T rS rT)
      (bop_product S T plusS plusT)
      (bop_product S T timesS timesT)
      (bop_product_id_equals_ann_decide S T rS rT timesS plusS timesT plusT pS_d pT_d)
   = 
   bop_product_times_id_equals_plus_ann_check S T
      (p2c_times_id_equals_plus_ann S rS plusS timesS pS_d) 
      (p2c_times_id_equals_plus_ann T rT plusT timesT pT_d). 
Proof. intros S T rS rT plusS timesS plusT timesT 
       [ eqS | neqS] [eqT | neqT] ; compute; reflexivity. 
Qed. 

(* treatment of witnesses is ugly ... *) 
Lemma bop_product_left_left_absorbtive_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (wS : brel_witness S rS)
    (wT : brel_witness T rT)
    (pS_d : bops_left_left_absorptive_decidable S rS plusS timesS) 
    (pT_d : bops_left_left_absorptive_decidable T rT plusT timesT), 
   bop_product_left_left_absorptive_check S T
       (projT1 wS)
       (projT1 wT)
       (p2c_left_left_absorptive S rS plusS timesS pS_d)
       (p2c_left_left_absorptive T rT plusT timesT pT_d)
     = 
     p2c_left_left_absorptive (S * T) 
        (brel_product S T rS rT)
        (bop_product S T plusS plusT)
        (bop_product S T timesS timesT)
        (bops_product_left_left_absorptive_decide S T 
             (brel_get_witness S rS wS) 
             (brel_get_witness T rT wT) 
             rS rT plusS timesS plusT timesT pS_d pT_d).
Proof. intros S T rS rT plusS timesS plusT timesT [s Ps] [t Pt]
       [ ldS | [ [s1 s2] nldS]] 
       [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. 
Qed. 


(* treatment of witnesses is ugly ... *) 
Lemma bop_product_left_right_absorbtive_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (wS : brel_witness S rS)
    (wT : brel_witness T rT)
    (pS_d : bops_left_right_absorptive_decidable S rS plusS timesS) 
    (pT_d : bops_left_right_absorptive_decidable T rT plusT timesT), 
   bop_product_left_right_absorptive_check S T
       (projT1 wS)
       (projT1 wT)
       (p2c_left_right_absorptive S rS plusS timesS pS_d)
       (p2c_left_right_absorptive T rT plusT timesT pT_d)
     = 
     p2c_left_right_absorptive (S * T) 
        (brel_product S T rS rT)
        (bop_product S T plusS plusT)
        (bop_product S T timesS timesT)
        (bops_product_left_right_absorptive_decide S T 
             (brel_get_witness S rS wS) 
             (brel_get_witness T rT wT) 
             rS rT plusS timesS plusT timesT pS_d pT_d).
Proof. intros S T rS rT plusS timesS plusT timesT [s Ps] [t Pt]
       [ ldS | [ [s1 s2] nldS]] 
       [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. 
Qed. 


(* treatment of witnesses is ugly ... *) 
Lemma bop_product_right_left_absorbtive_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (wS : brel_witness S rS)
    (wT : brel_witness T rT)
    (pS_d : bops_right_left_absorptive_decidable S rS plusS timesS) 
    (pT_d : bops_right_left_absorptive_decidable T rT plusT timesT), 
   bop_product_right_left_absorptive_check S T
       (projT1 wS)
       (projT1 wT)
       (p2c_right_left_absorptive S rS plusS timesS pS_d)
       (p2c_right_left_absorptive T rT plusT timesT pT_d)
     = 
     p2c_right_left_absorptive (S * T) 
        (brel_product S T rS rT)
        (bop_product S T plusS plusT)
        (bop_product S T timesS timesT)
        (bops_product_right_left_absorptive_decide S T 
             (brel_get_witness S rS wS) 
             (brel_get_witness T rT wT) 
             rS rT plusS timesS plusT timesT pS_d pT_d).
Proof. intros S T rS rT plusS timesS plusT timesT [s Ps] [t Pt]
       [ ldS | [ [s1 s2] nldS]] 
       [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. 
Qed. 


(* treatment of witnesses is ugly ... *) 
Lemma bop_product_right_right_absorbtive_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (wS : brel_witness S rS)
    (wT : brel_witness T rT)
    (pS_d : bops_right_right_absorptive_decidable S rS plusS timesS) 
    (pT_d : bops_right_right_absorptive_decidable T rT plusT timesT), 
   bop_product_right_right_absorptive_check S T
       (projT1 wS)
       (projT1 wT)
       (p2c_right_right_absorptive S rS plusS timesS pS_d)
       (p2c_right_right_absorptive T rT plusT timesT pT_d)
     = 
     p2c_right_right_absorptive (S * T) 
        (brel_product S T rS rT)
        (bop_product S T plusS plusT)
        (bop_product S T timesS timesT)
        (bops_product_right_right_absorptive_decide S T 
             (brel_get_witness S rS wS) 
             (brel_get_witness T rT wT) 
             rS rT plusS timesS plusT timesT pS_d pT_d).
Proof. intros S T rS rT plusS timesS plusT timesT [s Ps] [t Pt]
       [ ldS | [ [s1 s2] nldS]] 
       [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. 
Qed. 




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

(*

Lemma bops_llex_product_left_absorbtive_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (symS   : brel_symmetric S rS )
    (transS : brel_transitive S rS)
    (wtT : brel_witness T rT) 
    (refT   : brel_reflexive T rT)
    (pS_d : bops_left_absorptive_decidable S rS plusS timesS)
    (pT_d : bops_left_absorptive_decidable T rT  plusT timesT)
    (alS_d : bop_anti_left_decidable S rS timesS), 
   p2c_left_absorptive (S * T)
      (brel_product S T rS rT)
      (bop_llex S T rS plusS plusT)
      (bop_product S T timesS timesT)
      (bops_llex_product_left_absorptive_decide S T
         (brel_get_witness T rT wtT)
         rS rT plusS timesS plusT timesT symS transS refT pS_d pT_d alS_d)
   = 
   bops_llex_product_left_absorptive_check S T
      (projT1 wtT) 
      (p2c_left_absorptive S rS plusS timesS pS_d) 
      (p2c_left_absorptive T rT plusT timesT pT_d) 
      (p2c_anti_left_check S rS timesS alS_d). 
Proof. intros S T rS rT plusS timesS plusT timesT symS transS [t Pt] refT
       [ laS | [ [s1 s2] nlaS ] ]  [ laT | [ [t1 t2] nlaT ]]  [ alS | [ [s3 s4] nalS ]]; 
       compute; reflexivity. 
Qed. 

Lemma bops_llex_product_right_absorbtive_check_correct : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T)
    (symS   : brel_symmetric S rS )
    (transS : brel_transitive S rS)
    (wtT : brel_witness T rT) 
    (refT   : brel_reflexive T rT)
    (pS_d : bops_right_absorptive_decidable S rS plusS timesS)
    (pT_d : bops_right_absorptive_decidable T rT  plusT timesT)
    (alS_d : bop_anti_right_decidable S rS timesS), 
   p2c_right_absorptive (S * T)
      (brel_product S T rS rT)
      (bop_llex S T rS plusS plusT)
      (bop_product S T timesS timesT)
      (bops_llex_product_right_absorptive_decide S T
         (brel_get_witness T rT wtT)
         rS rT plusS timesS plusT timesT symS transS refT pS_d pT_d alS_d)
   = 
   bops_llex_product_right_absorptive_check S T
      (projT1 wtT) 
      (p2c_right_absorptive S rS plusS timesS pS_d) 
      (p2c_right_absorptive T rT plusT timesT pT_d) 
      (p2c_anti_right_check S rS timesS alS_d). 
Proof. intros S T rS rT plusS timesS plusT timesT symS transS [t Pt] refT
       [ laS | [ [s1 s2] nlaS ] ]  [ laT | [ [t1 t2] nlaT ]]  [ alS | [ [s3 s4] nalS ]]; 
       compute; reflexivity. 
Qed. 

*) 

(* add zero *) 

Lemma bops_add_zero_left_distributive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (refS : brel_reflexive S rS)
  (pS : bop_left_distributive_decidable S rS plusS timesS), 
  p2c_left_distributive (with_constant S)
     (brel_add_constant S rS c)                                  
     (bop_add_id S plusS c)
     (bop_add_ann S timesS c)
     (bops_add_zero_left_distributive_decide S rS c plusS timesS refS pS)
  = 
  bops_add_zero_left_distributive_check S (p2c_left_distributive S rS plusS timesS pS). 
Proof. intros S c rS plusS timesS refS [ ldS | [ [s1 [s2 s3]] nldS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma  bops_add_zero_right_distributive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (refS : brel_reflexive S rS)
  (pS : bop_right_distributive_decidable S rS plusS timesS), 
  p2c_right_distributive (with_constant S)
     (brel_add_constant S rS c)                                  
     (bop_add_id S plusS c)
     (bop_add_ann S timesS c)
     (bops_add_zero_right_distributive_decide S rS c plusS timesS refS pS)
  = 
  bops_add_zero_right_distributive_check S (p2c_right_distributive S rS plusS timesS pS). 
Proof. intros S c rS plusS timesS refS [ ldS | [ [s1 [s2 s3]] nldS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma bops_add_zero_times_id_equals_plus_ann_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_id_equals_ann_decidable S rS timesS plusS), 
  p2c_times_id_equals_plus_ann (with_constant S)
     (brel_add_constant S rS c)
     (bop_add_id S plusS c)
     (bop_add_ann S timesS c)
     (bops_add_zero_ann_equals_id_decide S rS 
        (brel_get_witness S rS (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS)))
        c plusS timesS (A_eqv_reflexive S rS eqvS) pS) 
  = 
  match p2c_times_id_equals_plus_ann S rS plusS timesS pS with 
  | Certify_Times_Id_Equals_Plus_Ann => Certify_Times_Id_Equals_Plus_Ann (with_constant S)
  | Certify_Not_Times_Id_Equals_Plus_Ann => Certify_Not_Times_Id_Equals_Plus_Ann (with_constant S)
  end. 
Proof. intros S c rS plusS timesS eqvS [ L | R]; compute; reflexivity. Qed. 



Lemma bops_add_zero_left_left_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_left_left_absorptive_decidable S rS plusS timesS), 
  p2c_left_left_absorptive(with_constant S)
     (brel_add_constant S rS c)                                  
     (bop_add_id S plusS c)
     (bop_add_ann S timesS c)
     (bops_add_zero_left_left_absorptive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_left_left_absorptive_check S 
     (projT1 (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS)))
     (p2c_left_left_absorptive S rS plusS timesS pS). 
Proof. intros S c rS plusS timesS eqvS [ ldS | [ [s1 s2] nldS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma bops_add_zero_left_right_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_left_right_absorptive_decidable S rS plusS timesS), 
  p2c_left_right_absorptive(with_constant S)
     (brel_add_constant S rS c)                                  
     (bop_add_id S plusS c)
     (bop_add_ann S timesS c)
     (bops_add_zero_left_right_absorptive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_left_right_absorptive_check S 
     (projT1 (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS)))
     (p2c_left_right_absorptive S rS plusS timesS pS). 
Proof. intros S c rS plusS timesS eqvS [ ldS | [ [s1 s2] nldS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma  bops_add_zero_right_left_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_right_left_absorptive_decidable S rS plusS timesS), 
  p2c_right_left_absorptive(with_constant S)
     (brel_add_constant S rS c)                                  
     (bop_add_id S plusS c)
     (bop_add_ann S timesS c)
     (bops_add_zero_right_left_absorptive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_right_left_absorptive_check S 
     (projT1 (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS)))
     (p2c_right_left_absorptive S rS plusS timesS pS). 
Proof. intros S c rS plusS timesS eqvS [ ldS | [ [s1 s2] nldS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma  bops_add_zero_right_right_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_right_right_absorptive_decidable S rS plusS timesS), 
  p2c_right_right_absorptive(with_constant S)
     (brel_add_constant S rS c)                                  
     (bop_add_id S plusS c)
     (bop_add_ann S timesS c)
     (bops_add_zero_right_right_absorptive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_right_right_absorptive_check S 
     (projT1 (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS)))
     (p2c_right_right_absorptive S rS plusS timesS pS). 
Proof. intros S c rS plusS timesS eqvS [ ldS | [ [s1 s2] nldS ] ]; 
       compute; reflexivity. 
Qed. 


(* add one *)

Lemma bops_add_one_plus_id_equals_times_ann_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_id_equals_ann_decidable S rS plusS timesS), 
  p2c_plus_id_equals_times_ann (with_constant S)
     (brel_add_constant S rS c)
     (bop_add_ann S plusS c)
     (bop_add_id S timesS c)
     (bops_add_one_id_equals_ann_decide S rS 
        (brel_get_witness S rS (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS)))
        c plusS timesS (A_eqv_reflexive S rS eqvS) pS) 
  = 
  match p2c_plus_id_equals_times_ann S rS plusS timesS pS with 
  | Certify_Plus_Id_Equals_Times_Ann => Certify_Plus_Id_Equals_Times_Ann (with_constant S)
  | Certify_Not_Plus_Id_Equals_Times_Ann => Certify_Not_Plus_Id_Equals_Times_Ann (with_constant S)
  end. 
Proof. intros S c rS plusS timesS eqvS [ L | R]; compute; reflexivity. Qed. 
 

Lemma bops_add_one_left_distributive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (refS : brel_reflexive S rS)
  (symS : brel_symmetric S rS)
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (llaS_d : bops_left_left_absorptive_decidable S rS plusS timesS) 
  (rlaS_d : bops_right_left_absorptive_decidable S rS plusS timesS) 
  (ldS_d : bop_left_distributive_decidable S rS plusS timesS), 
  p2c_left_distributive (with_constant S)
     (brel_add_constant S rS c)                                  
     (bop_add_ann S plusS c)
     (bop_add_id S timesS c)
     (bops_add_one_left_distributive_decide S rS c plusS timesS 
         refS symS idmS_d llaS_d rlaS_d ldS_d)
  = 
  bops_add_one_left_distributive_check S c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_left_absorptive S rS plusS timesS llaS_d)
     (p2c_right_left_absorptive S rS plusS timesS rlaS_d)
     (p2c_left_distributive S rS plusS timesS ldS_d). 
Proof. intros S c rS plusS timesS refS symS 
       [ idmS | [ s0 nidmS ] ] 
       [ llaS | [ [s1 s2] nllaS ] ]
       [ rlaS | [ [s6 s7] nrlaS ] ]
       [ ldS | [ [s3 [s4 s5]] nldS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma bops_add_one_right_distributive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (refS : brel_reflexive S rS)
  (symS : brel_symmetric S rS)
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (llaS_d : bops_left_right_absorptive_decidable S rS plusS timesS) 
  (rlaS_d : bops_right_right_absorptive_decidable S rS plusS timesS) 
  (ldS_d : bop_right_distributive_decidable S rS plusS timesS), 
  p2c_right_distributive (with_constant S)
     (brel_add_constant S rS c)                                  
     (bop_add_ann S plusS c)
     (bop_add_id S timesS c)
     (bops_add_one_right_distributive_decide S rS c plusS timesS 
         refS symS idmS_d llaS_d rlaS_d ldS_d)
  = 
  bops_add_one_right_distributive_check S c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_right_absorptive S rS plusS timesS llaS_d)
     (p2c_right_right_absorptive S rS plusS timesS rlaS_d)
     (p2c_right_distributive S rS plusS timesS ldS_d). 
Proof. intros S c rS plusS timesS refS symS 
       [ idmS | [ s0 nidmS ] ] 
       [ llaS | [ [s1 s2] nllaS ] ]
       [ rlaS | [ [s6 s7] nrlaS ] ]
       [ ldS | [ [s3 [s4 s5]] nldS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma bops_add_one_left_left_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (refS : brel_reflexive S rS)
  (symS : brel_symmetric S rS)
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_left_left_absorptive_decidable S rS plusS timesS), 
  p2c_left_left_absorptive (with_constant S)
     (brel_add_constant S rS c)                                  
     (bop_add_ann S plusS c)
     (bop_add_id S timesS c)
     (bops_add_one_left_left_absorptive_decide S rS c plusS timesS symS idmS_d laS_d)
  = 
  bops_add_one_left_left_absorptive_check S c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_left_absorptive S rS plusS timesS laS_d).
Proof. intros S c rS plusS timesS refS symS 
       [ idmS | [ s0 nidmS ] ] 
       [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma bops_add_one_left_right_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (refS : brel_reflexive S rS)
  (symS : brel_symmetric S rS)
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_left_right_absorptive_decidable S rS plusS timesS), 
  p2c_left_right_absorptive (with_constant S)
     (brel_add_constant S rS c)                                  
     (bop_add_ann S plusS c)
     (bop_add_id S timesS c)
     (bops_add_one_left_right_absorptive_decide S rS c plusS timesS symS idmS_d laS_d)
  = 
  bops_add_one_left_right_absorptive_check S c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_right_absorptive S rS plusS timesS laS_d).
Proof. intros S c rS plusS timesS refS symS 
       [ idmS | [ s0 nidmS ] ] 
       [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma bops_add_one_right_left_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (refS : brel_reflexive S rS)
  (symS : brel_symmetric S rS)
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_right_left_absorptive_decidable S rS plusS timesS), 
  p2c_right_left_absorptive (with_constant S)
     (brel_add_constant S rS c)                                  
     (bop_add_ann S plusS c)
     (bop_add_id S timesS c)
     (bops_add_one_right_left_absorptive_decide S rS c plusS timesS symS idmS_d laS_d)
  = 
  bops_add_one_right_left_absorptive_check S c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_right_left_absorptive S rS plusS timesS laS_d).
Proof. intros S c rS plusS timesS refS symS 
       [ idmS | [ s0 nidmS ] ] 
       [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma bops_add_one_right_right_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (refS : brel_reflexive S rS)
  (symS : brel_symmetric S rS)
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_right_right_absorptive_decidable S rS plusS timesS), 
  p2c_right_right_absorptive (with_constant S)
     (brel_add_constant S rS c)                                  
     (bop_add_ann S plusS c)
     (bop_add_id S timesS c)
     (bops_add_one_right_right_absorptive_decide S rS c plusS timesS symS idmS_d laS_d)
  = 
  bops_add_one_right_right_absorptive_check S c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_right_right_absorptive S rS plusS timesS laS_d).
Proof. intros S c rS plusS timesS refS symS 
       [ idmS | [ s0 nidmS ] ] 
       [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 






