Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.brel.eq_bool. 

Lemma eqb_orb_congruence : 
   ∀ s1 s2 t1 t2 : bool,
   eqb s1 t1 = true → eqb s2 t2 = true → eqb (s1 || s2) (t1 || t2) = true. 
Proof.    
   intros s1 s2 t1 t2 H1 H2. 
   assert (C1 := eqb_bool_to_prop s1 t1 H1). 
   assert (C2 := eqb_bool_to_prop s2 t2 H2). 
   rewrite C1. rewrite C2.  apply brel_eq_bool_reflexive. 
Defined. 

Lemma bop_or_congruence : bop_congruence bool brel_eq_bool bop_or.
Proof. unfold bop_congruence. unfold brel_eq_bool, bop_or.
       exact eqb_orb_congruence. 
Defined. 

Lemma bop_or_idempotent : bop_idempotent bool brel_eq_bool bop_or.
Proof. unfold bop_idempotent. induction s; simpl; reflexivity. Defined. 

Lemma bop_or_commutative : bop_commutative bool brel_eq_bool bop_or.
Proof. unfold bop_commutative. induction s; induction t; simpl; reflexivity. Defined. 

Lemma bop_or_selective : bop_selective bool brel_eq_bool bop_or.
Proof. unfold bop_selective. induction s; induction t; simpl. 
      right. reflexivity. left. reflexivity. right. reflexivity. right. reflexivity. 
Defined. 

Lemma bop_or_associative : bop_associative bool brel_eq_bool bop_or.
Proof. unfold bop_associative. induction s; induction t; induction u; simpl; reflexivity. Defined. 

Lemma bop_or_not_is_left : bop_not_is_left bool brel_eq_bool bop_or.
Proof. unfold bop_not_is_left. exists (false, true); simpl. reflexivity. Defined. 

Lemma bop_or_not_is_right : bop_not_is_right bool brel_eq_bool bop_or.
Proof. unfold bop_not_is_right. exists (true, false); simpl. reflexivity. Defined. 

Lemma bop_or_exists_id : bop_exists_id bool brel_eq_bool bop_or.
Proof. exists false. induction s; auto. Defined. 

Lemma bop_or_exists_ann : bop_exists_ann bool brel_eq_bool bop_or.
Proof. exists true. induction s; auto. Defined. 


Lemma bop_or_not_left_cancellative : bop_not_left_cancellative bool brel_eq_bool bop_or.
Proof. exists (true, (false, true)); simpl. auto. Defined. 

Lemma bop_or_not_right_cancellative : bop_not_right_cancellative bool brel_eq_bool bop_or.
Proof. exists (true, (false, true)); simpl. auto. Defined. 
  
Lemma bop_or_not_left_constant : bop_not_left_constant bool brel_eq_bool bop_or.
Proof. exists (false, (false, true)); simpl. auto. Defined. 

Lemma bop_or_not_right_constant : bop_not_right_constant bool brel_eq_bool bop_or.
Proof. exists (false, (false, true)); simpl. auto. Defined. 

Lemma bop_or_not_anti_left : bop_not_anti_left bool brel_eq_bool bop_or.
Proof. exists (true, false); simpl. auto. Defined. 

Lemma bop_or_not_anti_right : bop_not_anti_right bool brel_eq_bool bop_or.
Proof. exists (true, false); simpl. auto. Defined. 
