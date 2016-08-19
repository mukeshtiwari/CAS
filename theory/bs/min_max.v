Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.bs_properties. 
Require Import CAS.theory.brel.eq_nat. 
Require Import CAS.theory.bop.min. 
Require Import CAS.theory.bop.max. 
Require Import CAS.theory.facts. 



Lemma bops_min_max_left_left_absorptive  : 
     bops_left_left_absorptive nat brel_eq_nat bop_min bop_max. 
Proof. induction s; induction t; simpl; auto. 
       apply brel_eq_nat_symmetric. 
       apply bop_min_idempotent. 
Qed. 

Lemma bops_min_max_left_right_absorptive  : 
       bops_left_right_absorptive nat brel_eq_nat bop_min bop_max. 
Proof. apply bops_left_left_absorptive_implies_left_right.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_min_congruence. 
       apply bop_max_commutative. 
       apply bops_min_max_left_left_absorptive. 
Qed. 


Lemma bops_min_max_right_left_absorptive  : 
       bops_right_left_absorptive nat brel_eq_nat bop_min bop_max. 
Proof. apply bops_left_right_absorptive_implies_right_left.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_min_congruence. 
       apply bop_min_commutative. 
       apply bop_max_commutative. 
       apply bops_min_max_left_right_absorptive. 
Qed. 



Lemma bops_min_max_right_right_absorptive  : 
       bops_right_right_absorptive nat brel_eq_nat bop_min bop_max. 
Proof. apply bops_right_left_absorptive_implies_right_right.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_min_congruence. 
       apply bop_max_commutative. 
       apply bops_min_max_right_left_absorptive. 
Qed. 


Lemma bops_min_max_left_distributive  : 
     bop_left_distributive nat brel_eq_nat bop_min bop_max. 
Proof. unfold bop_left_distributive. 
       induction s; induction t; induction u; simpl; auto. 
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_symmetric. 
       apply bop_min_idempotent. 
       apply bops_min_max_left_left_absorptive. 
       assert (H := bop_min_commutative s (bop_max s t)). 
       assert (K : brel_eq_nat s (bop_min s (bop_max s t)) = true). 
          apply bops_min_max_left_left_absorptive. 
       assert (T := brel_eq_nat_transitive _ _ _ K H). 
       assumption. 
Qed. 

Lemma bops_min_max_right_distributive  : 
     bop_right_distributive nat brel_eq_nat bop_min bop_max. 
Proof. apply bop_left_distributive_implies_right. 
       exact brel_eq_nat_transitive. 
       exact bop_min_congruence. 
       exact bop_min_commutative. 
       exact bop_max_commutative. 
       exact bops_min_max_left_distributive. 
Qed. 

Lemma bops_min_max_ann_equals_id : 
      bops_id_equals_ann nat brel_eq_nat bop_max bop_min. 
Proof. exists bop_max_exists_id. exists bop_min_exists_ann. compute. reflexivity. Qed. 

Lemma bops_min_max_not_id_equals_ann : 
      bops_not_id_equals_ann nat brel_eq_nat bop_min bop_max. 
Proof. unfold bops_not_id_equals_ann. intros i a F1 F2. 
       destruct (bop_min_not_exists_id i) as [s [H | H]]. 
          destruct (F1 s) as [G1 G2]. 
          rewrite G1 in H. discriminate. 
          destruct (F1 s) as [G1 G2]. 
          rewrite G2 in H. discriminate. 
Qed. 




