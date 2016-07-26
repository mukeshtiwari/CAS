Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.brel.eq_nat. 


Lemma beq_nat_times_congruence : 
   ∀ s1 s2 t1 t2 : nat,
   beq_nat s1 t1 = true
   → beq_nat s2 t2 = true → beq_nat (mult s1 s2) (mult t1 t2) = true.
Proof. 
   intros s1 s2 t1 t2 H1 H2. 
   assert (C1 := beq_nat_to_prop s1 t1 H1). 
   assert (C2 := beq_nat_to_prop s2 t2 H2). 
   rewrite C1. rewrite C2.  apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_times_congruence : bop_congruence nat brel_eq_nat bop_times.
Proof. unfold bop_congruence. unfold brel_eq_nat, bop_times.
       exact beq_nat_times_congruence. 
Defined. 

Lemma bop_times_associative : bop_associative nat brel_eq_nat bop_times.
Proof. unfold bop_associative. intros. unfold brel_eq_nat, bop_times. 
       rewrite (Mult.mult_assoc s t u). apply brel_eq_nat_reflexive.        
Defined. 

Lemma bop_times_not_idempotent : bop_not_idempotent nat brel_eq_nat bop_times.
Proof. unfold bop_not_idempotent. exists 2. simpl. reflexivity. Defined. 

Lemma bop_times_commutative : bop_commutative nat brel_eq_nat bop_times.
Proof. unfold bop_commutative, bop_times. intros s t. 
       rewrite Mult.mult_comm at 1. apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_times_not_selective : bop_not_selective nat brel_eq_nat bop_times.
Proof. unfold bop_not_selective. exists (2, 2); simpl. split; reflexivity. 
Defined. 

Lemma bop_times_not_is_left : bop_not_is_left nat brel_eq_nat bop_times.
Proof. unfold bop_is_left. exists (1, 0); simpl. reflexivity. Defined. 

Lemma bop_times_not_is_right : bop_not_is_right nat brel_eq_nat bop_times.
Proof. unfold bop_not_is_left. exists (0, 1); simpl. reflexivity. Defined. 

Lemma bop_times_exists_id : bop_exists_id nat brel_eq_nat bop_times.
Proof. exists 1. intro s. unfold bop_times. split. 
       unfold mult. rewrite plus_comm. simpl. apply brel_eq_nat_reflexive. 
       rewrite mult_comm. simpl. rewrite plus_comm. simpl. apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_times_exists_ann : bop_exists_ann nat brel_eq_nat bop_times.
Proof. exists 0. intro s. unfold bop_times. split. 
       unfold mult. apply brel_eq_nat_reflexive. 
       rewrite mult_comm. simpl. reflexivity. 
Defined. 


Lemma  bop_times_not_left_cancellative : bop_not_left_cancellative nat brel_eq_nat bop_times.
Proof. exists (0, (0, 1)); simpl. auto. Defined. 


Lemma  bop_times_not_right_cancellative : bop_not_right_cancellative nat brel_eq_nat bop_times.
Proof. exists (0, (0, 1)); simpl. auto. Defined. 

Lemma bop_times_not_left_constant : bop_not_left_constant nat brel_eq_nat bop_times.
Proof. exists (1, (0, 1)); simpl. auto. Defined. 

Lemma bop_times_not_right_constant : bop_not_right_constant nat brel_eq_nat bop_times.
Proof. exists (1, (0, 1)); simpl. auto. Defined. 

Lemma bop_times_not_anti_left : bop_not_anti_left nat brel_eq_nat bop_times.
Proof. exists (0, 0); simpl. auto. Defined. 

Lemma bop_times_not_anti_right : bop_not_anti_right nat brel_eq_nat bop_times.
Proof. exists (0, 0); simpl. auto. Defined. 
