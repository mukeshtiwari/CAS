Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.bop_or. 
Require Import CAS.theory.bop_and. 




Lemma bops_and_or_left_distributive  : 
     bop_left_distributive bool brel_eq_bool bop_and bop_or. 
Proof. intros x y z. destruct x; destruct y; destruct z; compute; reflexivity. Qed. 

Lemma bops_and_or_right_distributive  : 
     bop_right_distributive bool brel_eq_bool bop_and bop_or.
Proof. intros x y z. destruct x; destruct y; destruct z; compute; reflexivity. Qed. 

Lemma bops_and_or_right_absorptive  : 
     bops_right_absorption bool brel_eq_bool bop_and bop_or.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 

Lemma bops_and_or_left_absorptive  : 
     bops_left_absorption bool brel_eq_bool bop_and bop_or.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 

Lemma bops_and_or_id_equals_ann : 
      bops_id_equals_ann bool brel_eq_bool bop_and bop_or. 
Proof. exists bop_and_exists_id. exists bop_or_exists_ann. compute. reflexivity. Qed. 

Lemma bops_and_or_ann_equals_id : 
      bops_id_equals_ann bool brel_eq_bool bop_or bop_and.
Proof. exists bop_or_exists_id. exists bop_and_exists_ann. compute. reflexivity. Qed. 





