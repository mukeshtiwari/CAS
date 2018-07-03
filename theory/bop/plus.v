Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.brel.eq_nat. 


Lemma beq_nat_plus_congruence : 
   ∀ s1 s2 t1 t2 : nat,
   beq_nat s1 t1 = true
   → beq_nat s2 t2 = true → beq_nat (plus s1 s2) (plus t1 t2) = true.
Proof. 
   intros s1 s2 t1 t2 H1 H2. 
   assert (C1 := beq_nat_to_prop s1 t1 H1). 
   assert (C2 := beq_nat_to_prop s2 t2 H2). 
   rewrite C1. rewrite C2.  apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_plus_congruence : bop_congruence nat brel_eq_nat bop_plus.
Proof. unfold bop_congruence. unfold brel_eq_nat, bop_plus.
       exact beq_nat_plus_congruence. 
Defined. 

Lemma bop_plus_associative : bop_associative nat brel_eq_nat bop_plus.
Proof. unfold bop_associative. intros. unfold brel_eq_nat, bop_plus. 
       rewrite (Plus.plus_assoc s t u). apply brel_eq_nat_reflexive.        
Defined. 

Lemma bop_plus_not_idempotent : bop_not_idempotent nat brel_eq_nat bop_plus.
Proof. unfold bop_not_idempotent. exists 1. simpl. reflexivity. Defined. 

Lemma bop_plus_commutative : bop_commutative nat brel_eq_nat bop_plus.
Proof. unfold bop_commutative, bop_plus. intros s t. 
       rewrite Plus.plus_comm at 1. apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_plus_not_selective : bop_not_selective nat brel_eq_nat bop_plus.
Proof. unfold bop_not_selective. exists (1, 1); simpl. split; reflexivity. 
Defined. 


Lemma bop_plus_not_is_left : bop_not_is_left nat brel_eq_nat bop_plus.
Proof. unfold bop_not_is_left. exists (0, 1); simpl. reflexivity. Defined. 

Lemma bop_plus_not_is_right : bop_not_is_right nat brel_eq_nat bop_plus.
Proof. unfold bop_not_is_left. exists (1, 0); simpl. reflexivity. Defined. 


Lemma bop_plus_zero_is_id : bop_is_id nat brel_eq_nat bop_plus 0.
Proof. intro s. unfold bop_plus. split. 
       unfold plus. apply brel_eq_nat_reflexive. 
       rewrite plus_comm. unfold plus. apply brel_eq_nat_reflexive. 
Qed. 

Lemma bop_plus_exists_id : bop_exists_id nat brel_eq_nat bop_plus.
Proof. exists 0. apply bop_plus_zero_is_id. Defined. 

Lemma bop_plus_S_left : ∀ s t : nat, bop_plus (S s) t = S (bop_plus s t). 
Proof. unfold bop_plus. induction s; induction t; compute; reflexivity. Defined. 

Lemma bop_plus_S_right : ∀ s t : nat, bop_plus s (S t) = S (bop_plus s t). 
Proof. intros s t. 
       assert(plus_comm_l := bop_plus_commutative s (S t)). apply beq_nat_to_prop in plus_comm_l. 
       assert(plus_comm_r := bop_plus_commutative s t). apply beq_nat_to_prop in plus_comm_r. 
       rewrite plus_comm_l, plus_comm_r.  
       apply bop_plus_S_left. 
Defined.


Lemma bop_plus_not_exists_ann : bop_not_exists_ann nat brel_eq_nat bop_plus.
Proof. unfold bop_not_exists_ann. induction a. 
       exists 1. left. compute. reflexivity. 
       destruct IHa as [s [H | H]]. 
          exists s. left.  rewrite bop_plus_S_left. rewrite brel_nat_eq_S. assumption. 
          exists s. right. rewrite bop_plus_S_right. rewrite brel_nat_eq_S. assumption. 
Defined. 


(* 
plus_Snm_nSm: ∀ n m : nat, S n + m = n + S m
plus_Sn_m: ∀ n m : nat, S n + m = S (n + m)
*) 
Lemma  bop_plus_left_cancellative : bop_left_cancellative nat brel_eq_nat bop_plus.
Proof. unfold bop_plus. unfold bop_left_cancellative. 
       induction s; intros t u.
       simpl. auto. 
       intro H. rewrite plus_Sn_m in H. rewrite plus_Sn_m in H. 
       rewrite brel_nat_eq_S in H. apply IHs; auto.  
Defined. 



Lemma  bop_plus_right_cancellative : bop_right_cancellative nat brel_eq_nat bop_plus.
Proof. unfold bop_plus, bop_right_cancellative. intros s t u H.
       rewrite plus_comm in H. (* does not work: rewrite plus_comm at 2. *) 
       apply brel_eq_nat_symmetric in H. 
       rewrite plus_comm in H. 
       apply brel_eq_nat_symmetric. 
       apply (bop_plus_left_cancellative _ _ _ H). 
Qed.        

Lemma bop_plus_not_left_constant : bop_not_left_constant nat brel_eq_nat bop_plus.
Proof. exists (0, (0, 1)); simpl. auto. Defined. 

Lemma bop_plus_not_right_constant : bop_not_right_constant nat brel_eq_nat bop_plus.
Proof. exists (0, (0, 1)); simpl. auto. Defined. 

Lemma bop_plus_not_anti_left : bop_not_anti_left nat brel_eq_nat bop_plus.
Proof. exists (0, 0); simpl. auto. Defined. 


Lemma bop_plus_not_anti_right : bop_not_anti_right nat brel_eq_nat bop_plus.
Proof. exists (0, 0); simpl. auto. Defined. 



