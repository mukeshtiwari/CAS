Require Import Coq.Arith.Arith.
Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.reduction.predicate.
Require Import CAS.coq.eqv.nat.
Require Import CAS.coq.eqv.predicate_reduce. 

Section Theory.
Open Scope nat.
(* This reduces nat to  
    {0, ... ceiling_minus_one, ceiling} 
    so that all n with ceiling_minus_one < n are identified with ceiling. 
    Note that this is non-trivial for all values of ceiling_minus_one : nat. 
*) 
Variable ceiling_minus_one : nat.  
Definition ceiling : nat := S (ceiling_minus_one).

Definition above_ceiling_minus_one : nat -> bool := λ n, ceiling_minus_one <? n.

Definition brel_nat_ceiling := brel_predicate_reduce ceiling above_ceiling_minus_one brel_eq_nat. 
  
Lemma above_ceiling_minus_one_congruence : pred_congruence nat brel_eq_nat above_ceiling_minus_one.
Proof. intros x y E. unfold above_ceiling_minus_one. apply beq_nat_to_prop in E. rewrite E. reflexivity. Qed.   

Lemma above_ceiling_minus_one_0 : above_ceiling_minus_one 0 = false. 
Proof. compute; auto. Qed. 

Lemma above_ceiling_minus_one_ceiling : above_ceiling_minus_one ceiling = true. 
Proof. apply Nat.ltb_lt. apply Nat.lt_succ_diag_r. Qed. 

Lemma brel_nat_ceiling_0_1 : brel_nat_ceiling  0 1 = false.
Proof. unfold brel_nat_ceiling. unfold brel_predicate_reduce. unfold brel_reduce.
       unfold uop_predicate_reduce.
       rewrite above_ceiling_minus_one_0.
       case_eq(above_ceiling_minus_one 1); intro H.
          unfold above_ceiling_minus_one in H. apply Nat.ltb_lt in H. apply Nat.lt_1_r in H. unfold ceiling. rewrite H. compute; auto. 
          compute; auto. 
Qed.

Definition brel_nat_ceiling_not_trivial_f (s : nat) := if above_ceiling_minus_one s then 0 else (S s).

Lemma brel_nat_ceiling_not_trivial : brel_not_trivial nat brel_nat_ceiling brel_nat_ceiling_not_trivial_f.
Proof. intro s.
       unfold brel_nat_ceiling. unfold brel_predicate_reduce. unfold uop_predicate_reduce. unfold brel_reduce. 
       case_eq(above_ceiling_minus_one s); intro H1;
       case_eq(above_ceiling_minus_one (brel_nat_ceiling_not_trivial_f s)); intro H2.
       unfold brel_nat_ceiling_not_trivial_f in H2. rewrite H1 in H2. rewrite above_ceiling_minus_one_0 in H2. discriminate H2. 
       unfold brel_nat_ceiling_not_trivial_f. rewrite H1. compute; auto.
       case_eq(brel_eq_nat s ceiling); intro H3.
          apply above_ceiling_minus_one_congruence in H3.
          rewrite above_ceiling_minus_one_ceiling in H3. rewrite H1 in H3. discriminate H3. 
          apply (brel_symmetric_implies_dual _ _ brel_eq_nat_symmetric) in H3. rewrite H3. auto.
       unfold brel_nat_ceiling_not_trivial_f. rewrite H1. split. apply brel_nat_neq_S.
       unfold brel_eq_nat. apply Nat.eqb_neq. apply Nat.neq_succ_diag_l.
Qed. 


Lemma brel_nat_ceiling_exactly_two : brel_eq_nat 0 ceiling_minus_one = true -> brel_exactly_two nat brel_nat_ceiling.
Proof.  intro H. exists (0, 1). unfold exactly_two. split. 
        apply brel_nat_ceiling_0_1.
        intro a. destruct a.
        left. compute; auto.
        right. unfold brel_nat_ceiling. unfold brel_predicate_reduce. unfold uop_predicate_reduce. unfold brel_reduce.
        unfold above_ceiling_minus_one.
        apply beq_nat_to_prop in H. rewrite <- H. simpl.
        apply brel_eq_nat_reflexive. 
Defined. 

Lemma brel_nat_ceiling_at_least_three : brel_eq_nat 0 ceiling_minus_one = false -> brel_at_least_three nat brel_nat_ceiling.
Proof. intro H. exists (0, (1, 2)).  split. split.
       apply brel_nat_ceiling_0_1. 
       unfold brel_nat_ceiling. unfold brel_predicate_reduce. unfold brel_reduce, uop_predicate_reduce, above_ceiling_minus_one.
       case_eq(ceiling_minus_one <? 0); intro H1; case_eq(ceiling_minus_one <? 2); intro H2.
       compute in H1. discriminate H1. compute in H1. discriminate H1. compute; auto. compute; auto.
       unfold brel_nat_ceiling. unfold brel_predicate_reduce. unfold brel_reduce, uop_predicate_reduce, above_ceiling_minus_one.       
       case_eq(ceiling_minus_one <? 1); intro H1; case_eq(ceiling_minus_one <? 2); intro H2.
       apply Nat.ltb_lt in H1.
       assert (H3 : ceiling_minus_one = 0). apply Nat.lt_1_r; auto. 
       rewrite H3 in H. compute in H. discriminate H.
       apply Nat.ltb_lt in H1.       
       assert (H3 : ceiling_minus_one = 0). apply Nat.lt_1_r; auto. 
       rewrite H3 in H. compute in H. discriminate H.
       apply Nat.ltb_lt in H2. assert (H4 : 1 < 2). apply Nat.lt_1_2.
       assert (H5 : 2 ≤ ceiling). admit. 
       assert (H6 : 1 < ceiling). admit.
       admit. 
       compute; auto. 
Admitted. 


Lemma brel_nat_ceiling_not_exactly_two :   brel_eq_nat 0 ceiling_minus_one = false -> brel_not_exactly_two nat brel_nat_ceiling.
Proof. intro H.
       apply brel_at_least_thee_implies_not_exactly_two.
       apply brel_predicate_reduce_symmetric. apply brel_eq_nat_symmetric.
       apply brel_predicate_reduce_transitive. apply brel_eq_nat_transitive.       
       apply brel_nat_ceiling_at_least_three; auto.       
Defined.

Lemma bel_nat_ceiling_exactly_two_decidable : brel_exactly_two_decidable nat brel_nat_ceiling. 
Proof. case_eq(brel_eq_nat 0 ceiling_minus_one); intro H.
       left. apply brel_nat_ceiling_exactly_two; auto. 
       right. apply brel_nat_ceiling_not_exactly_two; auto. 
Defined.

End Theory.

Section ACAS.

Definition A_eqv_nat_ceiling (ceiling_minus_one : nat) : A_eqv nat
  := A_eqv_predicate_reduce
       nat
       A_eqv_nat
       (S ceiling_minus_one)
       (above_ceiling_minus_one ceiling_minus_one)
       (brel_nat_ceiling_not_trivial_f ceiling_minus_one)
       (brel_nat_ceiling_not_trivial ceiling_minus_one)
       (bel_nat_ceiling_exactly_two_decidable ceiling_minus_one).       

End ACAS.

Section CAS.
Open Scope nat.

Definition eqv_nat_ceiling (ceiling_minus_one : nat) : @eqv nat
  := eqv_predicate_reduce
       (S ceiling_minus_one)
       (above_ceiling_minus_one ceiling_minus_one)
       (brel_nat_ceiling_not_trivial_f ceiling_minus_one)
       (if brel_eq_nat 0 ceiling_minus_one then Certify_Exactly_Two (1, 2) else Certify_Not_Exactly_Two (not_ex2 brel_eq_nat 0 1 2))
       eqv_eq_nat.
End CAS.

Section Verify.
Open Scope nat.

Lemma fact (ceiling_minus_one : nat) :
       p2c_exactly_two_check _ _ (bel_nat_ceiling_exactly_two_decidable ceiling_minus_one)
       = if brel_eq_nat 0 ceiling_minus_one then Certify_Exactly_Two (1, 2) else Certify_Not_Exactly_Two (not_ex2 brel_eq_nat 0 1 2).
Proof. unfold bel_nat_ceiling_exactly_two_decidable.
       (* case_eq(brel_eq_nat 0 ceiling_minus_one); intro H. *) 
Admitted.   

Theorem correct_eqv_nat (ceiling_minus_one : nat) : eqv_nat_ceiling ceiling_minus_one = A2C_eqv nat (A_eqv_nat_ceiling ceiling_minus_one). 
Proof. unfold eqv_nat_ceiling, A_eqv_nat_ceiling.
       rewrite <- fact. unfold brel_nat_ceiling. 
       rewrite <- correct_eqv_predicate_reduce. 
       reflexivity. 
Qed.        
  
End Verify.   
