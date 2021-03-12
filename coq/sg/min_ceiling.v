Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import Coq.Arith.Min.
Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.reduction.predicate.

Require Import CAS.coq.theory.reduction.full.


Require Import CAS.coq.eqv.nat.
Require Import CAS.coq.sg.plus.
Require Import CAS.coq.sg.min.
Require Import CAS.coq.eqv.nat_ceiling.


Section Theory.
  Open Scope nat.

  (* This reduces nat to  
    {0, ... ceiling_minus_one, ceiling} 
    so that all n with ceiling_minus_one < n are identified with ceiling. 
    Note that this is non-trivial for all values of ceiling_minus_one : nat. 
  *)

Variable ceiling_minus_one : nat.
(*  
Definition ceiling                 := nat_ceiling.ceiling ceiling_minus_one. 
Definition above_ceiling_minus_one := nat_ceiling.above_ceiling_minus_one ceiling_minus_one. 
Definition brel_nat_ceiling        := nat_ceiling.brel_nat_ceiling ceiling_minus_one. 
*)
Definition bop_min_ceiling         := bop_predicate_reduce (ceiling ceiling_minus_one) (above_ceiling_minus_one ceiling_minus_one) bop_min.

Lemma bop_min_ceiling_0_0 : bop_min_ceiling 0 0 = 0.
Proof. compute; auto. Qed. 

Lemma bop_min_ceiling_0_1 : bop_min_ceiling 0 1 = 0.
Proof. compute; auto. Qed.

Lemma bop_min_ceiling_1_0 : bop_min_ceiling 1 0 = 0.
Admitted. 

Lemma bop_min_ceiling_1_1 : bop_min_ceiling 1 1 = 1.
Admitted. 
 
Lemma above_ceiling_minus_one_min_intro (n m : nat) : ((above_ceiling_minus_one ceiling_minus_one m = true) * (above_ceiling_minus_one ceiling_minus_one n = true)) -> above_ceiling_minus_one ceiling_minus_one (bop_min m n) = true.
Proof. unfold above_ceiling_minus_one, bop_min.
       intros [H1 H2].
       apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2. apply Nat.ltb_lt.
       apply Nat.min_glb_lt; auto. 
Qed. 

Lemma above_ceiling_minus_one_min_elim (n m : nat) : above_ceiling_minus_one ceiling_minus_one (bop_min m n) = true -> (above_ceiling_minus_one ceiling_minus_one m = true) * (above_ceiling_minus_one ceiling_minus_one n = true).
Proof. unfold above_ceiling_minus_one, bop_min.
       intro H1.
       apply Nat.ltb_lt in H1. assert(H2 := Nat.lt_le_incl _ _ H1).
       assert (H3 := Nat.le_min_l m n).
       assert (H4 := Nat.le_min_r m n).
       assert (H5 := lt_not_le _ _ H1). 
       split; apply Nat.ltb_lt.
Admitted.


Lemma not_above_ceiling_minus_one_min_intro (n m : nat) : (above_ceiling_minus_one ceiling_minus_one m = false) + (above_ceiling_minus_one ceiling_minus_one n = false) -> above_ceiling_minus_one ceiling_minus_one (bop_min m n) = false.
Proof. unfold above_ceiling_minus_one, bop_min.
       intros [H1 | H1]; apply Nat.ltb_ge in H1; apply Nat.ltb_ge.
       assert (H2 := Nat.min_le_compat_r m ceiling_minus_one n H1). 
       assert (H3 := Nat.le_min_l ceiling_minus_one n). 
       assert (H4 := Nat.le_trans _ _ _ H2 H3). exact H4.
       assert (H2 := Nat.min_le_compat_l n ceiling_minus_one m H1). 
       assert (H3 := Nat.le_min_r m ceiling_minus_one). 
       assert (H4 := Nat.le_trans _ _ _ H2 H3). exact H4. 
Qed.        

Lemma not_above_ceiling_minus_one_min_elim (n m : nat) : above_ceiling_minus_one ceiling_minus_one (bop_min m n) = false -> (above_ceiling_minus_one ceiling_minus_one m = false) + (above_ceiling_minus_one ceiling_minus_one n = false).
Proof. unfold above_ceiling_minus_one, bop_min.
       intro H1. apply Nat.ltb_ge in H1.
       assert (H2 := Nat.min_le _ _ _ H1). 
Admitted.


Lemma above_ceiling_minus_one_implies_min (n : nat) : above_ceiling_minus_one ceiling_minus_one n = true -> bop_min (ceiling ceiling_minus_one) n = ceiling ceiling_minus_one.
Proof. unfold above_ceiling_minus_one.
       unfold bop_min. intro H.
       apply Nat.ltb_lt in H.
       assert (H2 : (ceiling ceiling_minus_one ) ≤ n). admit. 
Admitted. 

(*
Nat.le_min_l: ∀ n m : nat, Nat.min n m ≤ n
Nat.le_min_r: ∀ n m : nat, Nat.min n m ≤ m
le_min_r: ∀ n m : nat, Nat.min n m ≤ m
le_min_l: ∀ n m : nat, Nat.min n m ≤ n
Nat.min_le_compat_l: ∀ n m p : nat, n ≤ m → Nat.min p n ≤ Nat.min p m
Nat.min_le_compat_r: ∀ n m p : nat, n ≤ m → Nat.min n p ≤ Nat.min m p
Nat.max_min_disassoc: ∀ n m p : nat, Nat.min n (Nat.max m p) ≤ Nat.max (Nat.min n m) p
Nat.min_le: ∀ n m p : nat, Nat.min n m ≤ p → n ≤ p ∨ m ≤ p
Nat.min_le_compat: ∀ n m p q : nat, n ≤ m → p ≤ q → Nat.min n p ≤ Nat.min m q
Nat.min_le_iff: ∀ n m p : nat, Nat.min n m ≤ p ↔ n ≤ p ∨ m ≤ p
*) 

Lemma not_above_ceiling_minus_one_from_min (n m : nat): above_ceiling_minus_one ceiling_minus_one m = true -> above_ceiling_minus_one ceiling_minus_one (bop_min m n) = false -> above_ceiling_minus_one ceiling_minus_one n = false.
Proof. intros H1 H2. apply not_above_ceiling_minus_one_min_elim in H2. destruct H2 as [H2 | H2]; auto. 
       rewrite H1 in H2. discriminate H2. 
Qed.

Lemma above_and_below_min (n m : nat) : above_ceiling_minus_one ceiling_minus_one m = true -> above_ceiling_minus_one ceiling_minus_one n = false -> bop_min m n = n.
Proof. intros H1 H2.   unfold bop_min. unfold above_ceiling_minus_one in *.
       apply Nat.ltb_lt in H1. apply Nat.lt_le_incl in H1. apply Nat.ltb_ge in H2.
       assert (F := Nat.le_trans _ _ _ H2 H1).
       apply Nat.min_r; auto. 
Qed. 

Lemma ceiling_is_max_below (n : nat) : above_ceiling_minus_one ceiling_minus_one n = false -> bop_min (ceiling ceiling_minus_one) n = n.
Proof. intro H. unfold above_ceiling_minus_one in H. unfold bop_min. apply Nat.ltb_ge in H. apply Nat.min_r; auto.  Qed. 

(*
Lemma h' : forall m n: nat, m < n -> m<= n.
Proof. intros m n H. 
       rewrite le_lt_or_eq_iff.
       left. exact H.
Qed.

Lemma h : forall m n: nat, Nat.min m n = m -> m <= n.
Proof. intros m n H. rewrite <- H. apply le_min_r.
Qed.
*) 

Lemma pred_congruence_above_ceiling_minus_one : pred_congruence nat brel_eq_nat (above_ceiling_minus_one ceiling_minus_one).
Proof.  intros a b H. apply beq_nat_to_prop in H. rewrite H. reflexivity. Qed.

Lemma uop_congruence_above_ceiling_minus_one : uop_congruence nat brel_eq_nat (uop_predicate_reduce (ceiling ceiling_minus_one) (above_ceiling_minus_one ceiling_minus_one)). 
Proof. intros a b H. apply beq_nat_to_prop in H. rewrite H. apply brel_eq_nat_reflexive; auto. Qed.

Lemma uop_idempotent_above_ceiling_minus_one : uop_idempotent nat brel_eq_nat (uop_predicate_reduce (ceiling ceiling_minus_one) (above_ceiling_minus_one ceiling_minus_one)).
Proof. intros a. unfold uop_predicate_reduce. 
       case_eq(above_ceiling_minus_one ceiling_minus_one a); intro H1.
       rewrite above_ceiling_minus_one_ceiling.
       apply brel_eq_nat_reflexive.
       rewrite H1.
       apply brel_eq_nat_reflexive.
Qed.

(*
Lemma brel_nat_ceiling_congruence : brel_congruence nat brel_nat_ceiling brel_nat_ceiling.
Proof.
Admitted. 

Lemma brel_nat_ceiling_transitive : brel_transitive nat brel_nat_ceiling. 
Proof.
Admitted. 
 *)

Lemma bop_min_ceiling_congruence : bop_congruence nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling.
Proof. apply bop_predicate_reduce_congruence.
       apply brel_eq_nat_reflexive.
       apply pred_congruence_above_ceiling_minus_one. 
       apply bop_min_congruence. 
Qed.

Lemma bop_min_ceiling_idempotent : bop_idempotent nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling.
Proof.  apply bop_predicate_reduce_idempotent_intro_standard. 
        apply brel_eq_nat_reflexive.
        apply above_ceiling_minus_one_ceiling. 
        apply pred_congruence_above_ceiling_minus_one. 
        apply bop_min_idempotent.         
Qed. 

Lemma bop_min_ceiling_selective : bop_selective nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling.
Proof.  apply bop_predicate_reduce_selective. 
        apply brel_eq_nat_reflexive.
        apply above_ceiling_minus_one_ceiling. 
        apply pred_congruence_above_ceiling_minus_one.
        unfold above_ceiling_minus_one. 
           intros a b H1 H2.
           assert (H3 := bop_min_selective a b). 
           destruct H3 as [H3 | H3].
              admit.
              admit.         
        unfold bop_is_ann. split. 
           admit. (* false! *) 
           admit. 
        apply bop_min_selective.         
Admitted. 


Lemma bop_min_ceiling_commutative : bop_commutative nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling.
Admitted.
(*
Proof.  apply bop_predicate_reduce_commutative. 
        apply brel_eq_nat_reflexive.
        apply above_ceiling_minus_one_ceiling. 
        apply pred_congruence_above_ceiling_minus_one. 
        apply bop_min_idempotent.         
Qed. 
*) 


Lemma bop_left_uop_invariant_min_ceiling :
   bop_left_uop_invariant nat brel_eq_nat
                          (bop_reduce (uop_predicate_reduce (ceiling ceiling_minus_one) (above_ceiling_minus_one ceiling_minus_one)) bop_min)
                          (uop_predicate_reduce (ceiling ceiling_minus_one) (above_ceiling_minus_one ceiling_minus_one)). 
Proof. intros m n. unfold bop_reduce. unfold uop_predicate_reduce.
       case_eq(above_ceiling_minus_one ceiling_minus_one m); intro H1;
       case_eq(above_ceiling_minus_one ceiling_minus_one (bop_min m n)); intro H2. 
       case_eq(above_ceiling_minus_one ceiling_minus_one (bop_min (ceiling ceiling_minus_one) n)); intro H3.
          apply brel_eq_nat_reflexive.
          apply above_ceiling_minus_one_min_elim in H2. destruct H2 as [L R].
             apply above_ceiling_minus_one_implies_min in R. rewrite R. apply brel_eq_nat_reflexive.
       assert (H3 : above_ceiling_minus_one ceiling_minus_one (bop_min (ceiling ceiling_minus_one) n) = false).
          apply not_above_ceiling_minus_one_min_intro. right.
          apply not_above_ceiling_minus_one_min_elim in H2. destruct H2 as [H2 | H2].
          rewrite H1 in H2. discriminate H2. exact H2. 
       rewrite H3.
       assert (H4 := not_above_ceiling_minus_one_from_min _ _ H1 H2). 
       assert (H5 := above_and_below_min _ _ H1 H4). rewrite H5. 
       assert (H6 := ceiling_is_max_below _ H4). rewrite H6. 
       apply brel_eq_nat_reflexive.
       apply brel_eq_nat_reflexive.
       apply brel_eq_nat_reflexive.        
Qed. 

Lemma bop_right_uop_invariant_min_ceiling :
  bop_right_uop_invariant nat brel_eq_nat
                          (bop_reduce (uop_predicate_reduce (ceiling ceiling_minus_one) (above_ceiling_minus_one ceiling_minus_one)) bop_min)
                          (uop_predicate_reduce (ceiling ceiling_minus_one) (above_ceiling_minus_one ceiling_minus_one)). 
Admitted. 


Lemma bop_min_ceiling_associative : bop_associative nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling.
Admitted.
(*
Proof.
  apply bop_full_reduce_left_right_invariant_implies_associative.    <<<-- from CAS.coq.theory.reduction_full, put version in CAS.coq.theory.reduction_predicate.
  apply uop_congruence_above_ceiling_minus_one.
  apply bop_min_congruence; auto.  
  apply brel_eq_nat_reflexive; auto.
  apply brel_eq_nat_symmetric; auto.
  apply brel_eq_nat_transitive; auto. 
  apply uop_idempotent_above_ceiling_minus_one; auto.
  apply bop_min_associative; auto.
  apply bop_left_uop_invariant_min_ceiling; auto.
  apply bop_right_uop_invariant_min_ceiling; auto.
Qed.
*) 

Lemma bop_min_ceiling_not_is_left : bop_not_is_left nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling.
Proof. exists (1, 0).
       unfold brel_nat_ceiling.
       unfold brel_predicate_reduce, bop_predicate_reduce.
       unfold brel_reduce, uop_predicate_reduce.
       rewrite bop_min_ceiling_1_0. 
       rewrite above_ceiling_minus_one_0.
       case_eq(above_ceiling_minus_one ceiling_minus_one 1); intro H1; compute; auto.       
Defined. 

Lemma bop_min_ceiling_not_is_right : bop_not_is_right nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling.
Proof. exists (0, 1).
       unfold brel_nat_ceiling.
       unfold brel_predicate_reduce, bop_predicate_reduce.
       unfold brel_reduce, uop_predicate_reduce.
       rewrite bop_min_ceiling_0_1.
       rewrite above_ceiling_minus_one_0.       
       case_eq(above_ceiling_minus_one ceiling_minus_one 1); intro H1; compute; auto. 
Defined. 



Lemma bop_min_ceiling_not_exists_id : bop_not_exists_id nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling.
Proof. unfold bop_not_exists_id. intro i. 
       exists (S (bop_plus i (ceiling ceiling_minus_one))). left.
       unfold brel_nat_ceiling, bop_min_ceiling.
       unfold brel_predicate_reduce, bop_predicate_reduce.
       unfold brel_reduce, bop_full_reduce, uop_predicate_reduce.
       assert (F : above_ceiling_minus_one ceiling_minus_one (S (bop_plus i (ceiling ceiling_minus_one))) = false). admit.
       rewrite F.
       assert (M : bop_min (ceiling ceiling_minus_one) (S (bop_plus i (ceiling ceiling_minus_one))) = (ceiling ceiling_minus_one)). admit.
       assert (C : above_ceiling_minus_one ceiling_minus_one (ceiling ceiling_minus_one) = true). admit. 
       case_eq(above_ceiling_minus_one ceiling_minus_one i ); intro H1.
       rewrite M. rewrite C. rewrite C.
       admit. (* brel_eq_nat ceiling (S (bop_plus i ceiling)) = false *)
       assert (D : bop_min i (S (bop_plus i (ceiling ceiling_minus_one))) = i). admit. rewrite D.
       rewrite H1. rewrite H1. 
       admit. (* brel_eq_nat i (S (bop_plus i ceiling)) = false *)        
Admitted. 


Lemma bop_min_ceiling_zero_is_ann : bop_is_ann nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling 0.
Proof. intro s. split. 
       compute; auto.  
       assert (C := bop_min_ceiling_commutative s 0).
       assert (A : brel_nat_ceiling ceiling_minus_one (bop_min_ceiling 0 s) 0 = true). compute; auto.
       admit. (* assert (T := brel_nat_ceiling_transitive _ _ _ C A). *) 
       (* exact T. *) 
Admitted. 
  
Lemma bop_min_ceiling_exists_ann : bop_exists_ann nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling.
Proof. exists 0. apply bop_min_ceiling_zero_is_ann. Defined. 

Lemma bop_min_ceiling_not_left_cancellative : bop_not_left_cancellative nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling.
Proof. exists (0, (0, 1)). split. compute; auto. apply brel_nat_ceiling_0_1. Defined. 

Lemma bop_min_ceiling_not_right_cancellative : bop_not_right_cancellative nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling.
Proof. exists (0, (0, 1)). rewrite brel_nat_ceiling_0_1. rewrite bop_min_ceiling_0_0. rewrite bop_min_ceiling_1_0. split; auto. Defined. 
  
Lemma bop_min_ceiling_not_left_constant : bop_not_left_constant nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling.
Proof. exists (1, (0, 1)). rewrite bop_min_ceiling_1_0. rewrite bop_min_ceiling_1_1. rewrite brel_nat_ceiling_0_1; auto. Defined. 

Lemma bop_min_ceiling_not_right_constant : bop_not_right_constant nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling.
Proof. exists (1, (0, 1)). rewrite bop_min_ceiling_0_1. rewrite bop_min_ceiling_1_1. rewrite brel_nat_ceiling_0_1; auto. Defined. 

Lemma bop_min_ceiling_not_anti_right : bop_not_anti_right nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling.
Proof. exists (0, 1). rewrite bop_min_ceiling_1_0. compute; auto. Defined. 

Lemma bop_min_ceiling_not_anti_left : bop_not_anti_left nat (brel_nat_ceiling ceiling_minus_one) bop_min_ceiling.
Proof. exists (0, 1). rewrite bop_min_ceiling_0_1. compute; auto. Defined. 

End Theory.

Section ACAS.
(*  
Definition sg_CS_proofs_min_ceiling (ceiling_minus_one : nat) : sg_CS_proofs nat (brel_nat_ceiling ceiling_minus_one) (bop_min_ceiling ceiling_minus_one) := 
{| 
  A_sg_CS_associative  := bop_min_ceiling_associative ceiling_minus_one
; A_sg_CS_congruence   := bop_min_ceiling_congruence ceiling_minus_one
; A_sg_CS_commutative  := bop_min_ceiling_commutative ceiling_minus_one
; A_sg_CS_selective    := bop_min_ceiling_selective ceiling_minus_one
; A_sg_CS_exists_id_d  := inr _ (bop_min_ceiling_not_exists_id ceiling_minus_one)
; A_sg_CS_exists_ann_d := inl _ (bop_min_ceiling_exists_ann ceiling_minus_one)
|}. 



Definition A_sg_CS_min (ceiling_minus_one : nat) : A_sg_CS nat 
:= {| 
     A_sg_CS_eqv         := A_eqv_nat_ceiling ceiling_minus_one 
   ; A_sg_CS_bop         := bop_min_ceiling ceiling_minus_one 
   ; A_sg_CS_proofs      := sg_CS_proofs_min_ceiling ceiling_minus_one
   ; A_sg_CS_bop_ast     := Ast_bop_min        (* FIX *) 
   ; A_sg_CS_ast         := Ast_sg_CS_min      (* FIX *) 
   |}. 
*)

End ACAS.


Section CAS.
Open Scope nat.   
(*
Definition sg_CS_certs_min : @sg_CS_certificates nat 
:= {|
     sg_CS_associative        := Assert_Associative 
   ; sg_CS_congruence         := Assert_Bop_Congruence 
   ; sg_CS_commutative        := Assert_Commutative 
   ; sg_CS_selective          := Assert_Selective 
   ; sg_CS_exists_id_d        := Certify_Not_Exists_Id 
   ; sg_CS_exists_ann_d       := Certify_Exists_Ann 0
   |}. 



Definition sg_CS_min : @sg_CS nat 
:= {| 
     sg_CS_eqv   := eqv_eq_nat 
    ; sg_CS_bop   := bop_min_ceiling 
   ; sg_CS_certs := sg_CS_certs_min
   ; sg_CS_bop_ast := Ast_bop_min    (* FIX *) 
   ; sg_CS_ast     := Ast_sg_CS_min  (* FIX *) 
   |}. 
  
*)
End CAS.

Section Verify.
(*
Theorem correct_sg_CS_min : sg_CS_min = A2C_sg_CS nat (A_sg_CS_min). 
Proof. compute. reflexivity. Qed. 
*) 
End Verify.   
  