Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.brel_eq_nat. 
Require Import CAS.theory.bop_min. 
Require Import CAS.theory.bop_max. 

Lemma bops_max_min_left_distributive  : 
     bop_left_distributive nat brel_eq_nat bop_max bop_min. 
Proof. unfold bop_left_distributive. 
       induction s; induction t; induction u; simpl; auto. 
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_reflexive. 
Qed. 

Lemma bops_max_min_right_distributive  : 
     bop_right_distributive nat brel_eq_nat bop_max bop_min. 
Proof. unfold bop_right_distributive. 
       induction s; induction t; induction u; simpl; auto. 
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_reflexive. 
Qed. 

Lemma bops_max_min_right_absorptive  : 
     bops_right_absorption nat brel_eq_nat bop_max bop_min. 
Proof. unfold bops_right_absorption. 
       induction s; induction t; simpl; auto. 
       apply brel_eq_nat_reflexive. 
Qed. 

Lemma bops_max_min_left_absorptive  : 
     bops_left_absorption nat brel_eq_nat bop_max bop_min. 
Proof. unfold bops_left_absorption. 
       induction s; induction t; simpl; auto. 
       apply brel_eq_nat_reflexive. 
Qed. 

Lemma bops_max_min_id_equals_ann : 
      bops_id_equals_ann nat brel_eq_nat bop_max bop_min. 
Proof. exists bop_max_exists_id. exists bop_min_exists_ann. compute. reflexivity. Qed. 

Lemma bops_max_min_not_ann_equals_id : 
      bops_not_id_equals_ann nat brel_eq_nat bop_min bop_max. 
Proof. unfold bops_not_id_equals_ann. intros i a F1 F2. 
       destruct (bop_max_not_exists_ann a) as [s [H | H]]. 
          destruct (F2 s) as [G1 G2]. 
          rewrite G1 in H. discriminate. 
          destruct (F2 s) as [G1 G2]. 
          rewrite G2 in H. discriminate. 
Qed. 
