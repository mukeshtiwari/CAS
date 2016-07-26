Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import Coq.Arith.Min. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.eq_nat.
Require Import CAS.theory.bop.plus. 
Require Import CAS.theory.bop.max. 

Lemma max_add_l : ∀ u s : nat, u + s = max (u + s) s. 
Proof. induction u; induction s; simpl. 
       reflexivity. 
       simpl in IHs. rewrite <- IHs. reflexivity. 
       reflexivity. 
       apply injection_S. rewrite plus_Snm_nSm in IHs. assumption. 
Defined. 

Lemma max_add_r : ∀ u s : nat, u + s = max s (u + s). 
Proof. induction u; induction s; simpl. 
       reflexivity. 
       simpl in IHs. rewrite <- IHs. reflexivity. 
       reflexivity. 
       apply injection_S. rewrite plus_Snm_nSm in IHs. assumption. 
Defined. 

Lemma max_0_l : ∀ s : nat, s = max s 0. 
Proof. induction s; simpl; reflexivity. Qed. 

Lemma max_0_r : ∀ s : nat, s = max 0 s. 
Proof. intro s; compute. reflexivity. Qed. 

Lemma plus_0 : ∀ s : nat, s = s + 0. 
Proof. induction s; simpl. reflexivity. rewrite <- IHs. reflexivity. Qed. 


Lemma S_cong : ∀ s t : nat, brel_eq_nat s t = true -> brel_eq_nat (S s) (S t) = true. 
Proof. induction s; induction t; simpl; auto. Qed. 

Lemma S_cong_neg : ∀ s t : nat, brel_eq_nat s t = false -> brel_eq_nat (S s) (S t) = false. 
Proof. induction s; induction t; simpl; auto. Qed. 

(* distributivity *) 

(* a + (b max c) = (a + c) max (b + c) *) 
Lemma bop_max_plus_left_distributive : 
        bop_left_distributive nat brel_eq_nat bop_max bop_plus. 
Proof. unfold bop_left_distributive, bop_plus, bop_max. 
       induction s. 
          intros t u. simpl. apply brel_eq_nat_reflexive.
          induction t. 
             simpl. rewrite plus_comm. simpl. intro u.  
             rewrite Max.max_comm. rewrite plus_comm. rewrite <- max_add_l. 
             apply brel_eq_nat_reflexive.
             induction u; simpl. 
                rewrite <- plus_0. rewrite plus_comm. rewrite <- max_add_l. 
                apply brel_eq_nat_reflexive.
                rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. 
                rewrite bop_max_S. 
                apply S_cong. unfold bop_max. 
                apply IHs. 
Qed. 

Lemma bop_max_plus_right_distributive : 
        bop_right_distributive nat brel_eq_nat bop_max bop_plus. 
Proof. apply bops_left_distributive_and_times_commutative_imply_right_distributive. 
       apply brel_eq_nat_congruence. 
       apply bop_max_congruence. 
       apply bop_plus_commutative. 
       apply bop_max_plus_left_distributive. 
Defined. 

(*
      a max (b + c) <> (a + b) max (a + c)
 2 =  0 max (1 + 1) <> (0 + 1) max (0 + 1) = 1

Lemma bop_plus_max_not_left_distributive : 
        bop_not_left_distributive nat brel_eq_nat bop_plus bop_max.
Proof. exists (2, (1, 1)); compute. reflexivity. Defined. 

Lemma bop_plus_max_not_right_distributive : 
        bop_not_right_distributive nat brel_eq_nat bop_plus bop_max.
Proof. exists (2, (1, 1)); compute. reflexivity. Defined. 

*) 

(*
  s <> s + (s max t) 
  1 <> 1 + (1 max 1) = 2

Lemma bops_plus_max_not_left_absorption : 
        bops_not_left_absorption nat brel_eq_nat bop_plus bop_max. 
Proof. exists (1, 1); compute. reflexivity. Defined. 

Lemma bops_plus_max_not_right_absorption : 
        bops_not_right_absorption nat brel_eq_nat bop_plus bop_max. 
Proof. exists (1, 1); compute. reflexivity. Defined. 
*) 


(* special elements 

 id(plus) = 0 
ann(plus) = NONE 

 id(max) = 0 
ann(max) = NONE 

*) 


Lemma plus_1 : ∀ s : nat, brel_eq_nat (bop_plus 1 s) s = false. 
Proof. induction s. compute. reflexivity. 
       unfold bop_plus.  rewrite <- plus_n_Sm. apply S_cong_neg. 
       assumption. 

Qed. 

Lemma max_S_false : ∀ s : nat, brel_eq_nat (bop_max (S s) s) s = false. 
Proof. induction s. compute. reflexivity. 
       unfold bop_max.  rewrite bop_max_S. apply S_cong_neg. 
       assumption. 
Qed. 

Lemma bop_max_plus_not_id_equals_ann : 
        bops_not_id_equals_ann nat brel_eq_nat bop_max bop_plus. 
Proof. unfold bops_not_id_equals_ann. 
       unfold bop_is_id, bop_is_ann. 
       intros i a H1 H2. 
       destruct (H2 1) as [L R]. 
       destruct a. 
          compute in L. discriminate.
          rewrite plus_1 in R. discriminate.
Qed. 

Lemma bop_plus_max_not_id_equals_ann : 
        bops_not_id_equals_ann nat brel_eq_nat bop_plus bop_max. 
Proof. unfold bops_not_id_equals_ann. 
       unfold bop_is_id, bop_is_ann. 
       intros i a H1 H2. 
       destruct (H2 (S a)) as [L R]. 
       destruct a. 
          compute in L. discriminate.
          rewrite max_S_false in R. discriminate.
Qed. 

(* absorption *) 

Lemma bops_max_plus_not_left_left_absorptive : 
        bops_not_left_left_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute. reflexivity. Defined. 

Lemma bops_max_plus_not_left_right_absorptive : 
        bops_not_left_right_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute. reflexivity. Defined. 

Lemma bops_max_plus_not_right_left_absorptive : 
        bops_not_right_left_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute. reflexivity. Defined. 

Lemma bops_max_plus_not_right_right_absorptive : 
        bops_not_right_right_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute. reflexivity. Defined. 
