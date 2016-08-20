Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.brel_properties. 


Lemma brel_to_bool_congruence : brel_congruence bool brel_eq_bool brel_to_bool. 
Proof. induction s; induction t; induction u; induction v; intros H Q; auto. Qed. 

Lemma brel_to_bool_reflexive : brel_reflexive bool brel_to_bool. 
Proof. induction s; simpl; auto. Qed. 

Lemma brel_to_bool_transitive : brel_transitive bool brel_to_bool. 
Proof. induction s; induction t; simpl; intros u H1 H2; destruct u; auto.  Qed. 

Lemma brel_to_bool_antisymmetric : brel_antisymmetric bool brel_eq_bool brel_to_bool. 
Proof. induction s; induction t; simpl; intros; auto. Qed. 

Lemma brel_to_bool_total : brel_total bool brel_to_bool. 
Proof. induction s; induction t; simpl; auto. Qed. 


Lemma brel_to_bool_exists_bottom : brel_exists_bottom bool brel_to_bool. 
Proof. exists false. intro s. destruct s; compute; auto. Defined. 

Lemma brel_to_bool_exists_top : brel_exists_top bool brel_to_bool. 
Proof. exists true. intro s. destruct s; compute; auto. Defined. 
