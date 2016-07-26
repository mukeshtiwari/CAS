Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import Coq.Arith.Min. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.eq_nat.
Require Import CAS.theory.bop.plus. 
Require Import CAS.theory.bop.min. 

Lemma min_add : ∀ u s : nat, min (u + s) s = s. 
Proof. induction u; induction s; simpl. 
       reflexivity. 
       simpl in IHs. rewrite IHs. reflexivity. 
       reflexivity. 
       apply injection_S. rewrite plus_Snm_nSm in IHs. assumption. 
Defined. 


(* a + (b min c) = (a + c) min (b + c) *) 
Lemma bop_min_plus_left_distributive : 
        bop_left_distributive nat brel_eq_nat bop_min bop_plus. 
Proof. unfold bop_left_distributive, bop_plus, bop_min. 
       induction s. 
          intros t u. simpl. apply brel_eq_nat_reflexive.
          induction t. 
             simpl. rewrite plus_comm. simpl. intro u.  
             rewrite Min.min_comm. rewrite plus_comm. rewrite min_add. 
             apply brel_eq_nat_reflexive.
             induction u. 
                simpl. rewrite plus_comm. simpl. rewrite plus_comm. rewrite min_add. 
                apply brel_eq_nat_reflexive.
                rewrite plus_SS.  rewrite plus_SS. rewrite bop_min_S.  rewrite bop_min_S. 
                rewrite plus_SS.  apply injection_S_brel_eq_nat. apply IHs. 
Qed. 

Lemma bop_min_plus_right_distributive : 
        bop_right_distributive nat brel_eq_nat bop_min bop_plus. 
Proof. apply bops_left_distributive_and_times_commutative_imply_right_distributive. 
       apply brel_eq_nat_congruence. 
       apply bop_min_congruence. 
       apply bop_plus_commutative. 
       apply bop_min_plus_left_distributive. 
Defined. 

Lemma plus_lemma_1 : ∀ (a b : nat), plus a b = b -> a = 0. 
Proof. induction a. 
          auto. 
          induction b; intro H. 
             rewrite plus_comm in H. simpl in H. assumption. 
             elim IHb; auto.              
             assert (F: S a + S b = S (S a + b)). 
                rewrite plus_comm at 1. 
                rewrite plus_Sn_m at 1. 
                rewrite plus_comm at 1. reflexivity. 
             rewrite F in H.  apply injective_S in H. assumption.              
Defined. 

Lemma plus_idem_only_zero : ∀ (a : nat), plus a a = a -> a = 0. 
Proof. intro a. apply plus_lemma_1. Defined. 

Lemma bop_min_plus_not_id_equals_ann : 
        bops_not_id_equals_ann nat brel_eq_nat bop_min bop_plus. 
Proof. unfold bops_not_id_equals_ann. intros i a H K. 
       unfold bop_is_id in H. unfold bop_is_ann in K. 
       case_eq(brel_eq_nat i a); intro J. 
          assert(Ka := K a). destruct Ka as [LKa RKa]. 
          assert (fact : brel_eq_nat (bop_plus a a) a = true -> a = 0). 
             unfold bop_plus. intro Q. apply beq_nat_to_prop in Q. 
             apply plus_idem_only_zero; auto. 
          assert (E := fact RKa). rewrite E in J. 
          apply beq_nat_to_prop in J.  rewrite J in H. 
          destruct (H 1) as [F _]. compute in F.  discriminate. 
       reflexivity. 
Defined. 

Lemma bop_min_plus_ann_equals_id : 
        bops_id_equals_ann nat brel_eq_nat bop_plus bop_min.
Proof. unfold bops_id_equals_ann. 
       exists bop_plus_exists_id. exists bop_min_exists_ann. compute; auto. 
Defined. 


(* absorption *) 

Lemma bops_min_plus_left_left_absorptive : 
        bops_left_left_absorptive nat brel_eq_nat bop_min bop_plus. 
Proof. unfold bops_left_left_absorptive, bop_plus, bop_min, brel_eq_nat. 
       (* ugly --- cleanup ... *) 
       induction s. intro t. compute. reflexivity. 
       induction t. rewrite plus_comm. unfold plus. 
       assert (A := bop_min_idempotent). 
       unfold bop_idempotent in A. 
       assert (B := brel_eq_nat_symmetric). unfold brel_symmetric in B. 
       rewrite B. reflexivity. apply A. 
       rewrite plus_comm. rewrite min_comm. rewrite min_add. 
       apply brel_eq_nat_reflexive. 
Qed. 


Lemma bops_min_plus_left_right_absorptive  : 
       bops_left_right_absorptive nat brel_eq_nat bop_min bop_plus. 
Proof. apply bops_left_left_absorptive_implies_left_right.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_min_congruence. 
       apply bop_plus_commutative. 
       apply bops_min_plus_left_left_absorptive. 
Qed. 


Lemma bops_min_plus_right_left_absorptive  : 
       bops_right_left_absorptive nat brel_eq_nat bop_min bop_plus. 
Proof. apply bops_left_right_absorptive_implies_right_left.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_min_congruence. 
       apply bop_min_commutative. 
       apply bop_plus_commutative. 
       apply bops_min_plus_left_right_absorptive. 
Qed. 



Lemma bops_min_plus_right_right_absorptive  : 
       bops_right_right_absorptive nat brel_eq_nat bop_min bop_plus. 
Proof. apply bops_right_left_absorptive_implies_right_right.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_min_congruence. 
       apply bop_plus_commutative. 
       apply bops_min_plus_right_left_absorptive. 
Qed. 


