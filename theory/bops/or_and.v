Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.bop.or. 
Require Import CAS.theory.bop.and. 




Lemma bops_or_and_left_distributive  : 
     bop_left_distributive bool brel_eq_bool bop_or bop_and.
Proof. intros x y z. destruct x; destruct y; destruct z; compute; reflexivity. Qed. 

Lemma bops_or_and_right_distributive  : 
     bop_right_distributive bool brel_eq_bool bop_or bop_and.
Proof. intros x y z. destruct x; destruct y; destruct z; compute; reflexivity. Qed. 

Lemma bops_or_and_id_equals_ann : 
      bops_id_equals_ann bool brel_eq_bool bop_or bop_and.
Proof. exists bop_or_exists_id. exists bop_and_exists_ann. compute. reflexivity. Qed. 

Lemma bops_or_and_ann_equals_id : 
      bops_id_equals_ann bool brel_eq_bool bop_and bop_or. 
Proof. exists bop_and_exists_id. exists bop_or_exists_ann. compute. reflexivity. Qed. 

Lemma bops_or_and_left_left_absorptive  : 
     bops_left_left_absorptive bool brel_eq_bool bop_or bop_and.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 

Lemma bops_or_and_left_right_absorptive  : 
     bops_left_right_absorptive bool brel_eq_bool bop_or bop_and.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 

Lemma bops_or_and_right_left_absorptive  : 
     bops_right_left_absorptive bool brel_eq_bool bop_or bop_and.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 

Lemma bops_or_and_right_right_absorptive  : 
     bops_right_right_absorptive bool brel_eq_bool bop_or bop_and.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 


