Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import Coq.Arith.Min. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel_eq_nat.

Lemma beq_nat_min_congruence : 
   ∀ s1 s2 t1 t2 : nat,
   beq_nat s1 t1 = true
   → beq_nat s2 t2 = true → beq_nat (min s1 s2) (min t1 t2) = true.
Proof. 
   intros s1 s2 t1 t2 H1 H2. 
   assert (C1 := beq_nat_to_prop s1 t1 H1). 
   assert (C2 := beq_nat_to_prop s2 t2 H2). 
   rewrite C1. rewrite C2.  apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_min_congruence : bop_congruence nat brel_eq_nat bop_min.
Proof. unfold bop_congruence. unfold brel_eq_nat, bop_min.
       exact beq_nat_min_congruence. 
Defined. 

Lemma bop_min_associative : bop_associative nat brel_eq_nat bop_min.
Proof. unfold bop_associative. intros. unfold brel_eq_nat, bop_min. 
       rewrite (Min.min_assoc s t u). apply brel_eq_nat_reflexive.        
Defined. 


Lemma bop_min_idempotent : bop_idempotent nat brel_eq_nat bop_min.
Proof. unfold bop_idempotent, bop_min. induction s; simpl. 
       reflexivity. 
       assumption. 
Defined. 

Lemma bop_min_commutative : bop_commutative nat brel_eq_nat bop_min.
Proof. unfold bop_commutative, bop_min. intros s t. 
       rewrite Min.min_comm at 1. apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_min_selective : bop_selective nat brel_eq_nat bop_min.
Proof. unfold bop_selective. induction s; induction t; simpl. 
      right. reflexivity. left. reflexivity. right. reflexivity. apply IHs. 
Defined. 

Lemma bop_min_not_is_left : bop_not_is_left nat brel_eq_nat bop_min.
Proof. unfold bop_not_is_left. exists (1, 0); simpl. reflexivity. Defined. 

Lemma bop_min_not_is_right : bop_not_is_right nat brel_eq_nat bop_min.
Proof. unfold bop_not_is_left. exists (0, 1); simpl. reflexivity. Defined. 


Lemma bop_min_S : ∀ s t : nat, bop_min (S s) (S t) = S (bop_min s t). 
Proof. unfold bop_min. induction s; induction t; compute; reflexivity. Defined. 

Lemma bop_min_not_exists_id : bop_not_exists_id nat brel_eq_nat bop_min.
Proof. unfold bop_not_exists_id. induction i. 
       exists 1. left. compute. reflexivity. 
       destruct IHi as [s [H | H]]. 
          exists (S s). left.  rewrite bop_min_S. rewrite brel_nat_eq_S. assumption. 
          exists (S s). right.  rewrite bop_min_S. rewrite brel_nat_eq_S. assumption. 
Defined. 

Lemma bop_min_exists_ann : bop_exists_ann nat brel_eq_nat bop_min.
Proof. exists 0. intro s. unfold bop_min. split. 
       unfold min. apply brel_eq_nat_reflexive. 
       rewrite min_comm. unfold min. apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_min_not_left_cancellative : bop_not_left_cancellative nat brel_eq_nat bop_min.
Proof. exists (0, (0, 1)); simpl. auto. Defined. 

Lemma bop_min_not_right_cancellative : bop_not_right_cancellative nat brel_eq_nat bop_min.
Proof. exists (0, (0, 1)); simpl. auto. Defined. 
  
Lemma bop_min_not_left_constant : bop_not_left_constant nat brel_eq_nat bop_min.
Proof. exists (1, (0, 1)); simpl. auto. Defined. 

Lemma bop_min_not_right_constant : bop_not_right_constant nat brel_eq_nat bop_min.
Proof. exists (1, (0, 1)); simpl. auto. Defined. 

Lemma bop_min_not_anti_right : bop_not_anti_right nat brel_eq_nat bop_min.
Proof. exists (0, 1); simpl. auto. Defined. 

Lemma bop_min_not_anti_left : bop_not_anti_left nat brel_eq_nat bop_min.
Proof. exists (0, 1); simpl. auto. Defined. 

