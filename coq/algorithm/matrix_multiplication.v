From Coq Require Import
     List
     BinNatDef.
From CAS Require Import
     coq.common.compute     
     coq.eqv.properties
     coq.eqv.list
     coq.eqv.nat
     coq.uop.properties     
     coq.sg.properties
     coq.bs.properties
     coq.algorithm.matrix_definition
     coq.algorithm.matrix_algorithms
     coq.algorithm.matrix_addition. 
Import ListNotations.



Section Matrix_Multiplication.

  Variables
    (R : Type)
    (eqR  : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR mulR: binary_op R)
    (congrP : bop_congruence R eqR plusR)
    (congrM : bop_congruence R eqR mulR)
    (congrR : brel_congruence R eqR eqR).

(*  
  Fixpoint sum_fn (f : Node -> R) (l : list Node) : R :=
    match l with 
    | [] => zeroR
    | h :: t => plusR(f h)(sum_fn f t)
    end.

  Definition sum_fn (f : Node -> R) (l : list Node) : list Node → R :=
    fold_right (fun x => fun y => plusR (f x) y) zeroR.
 *)

  Local Definition domain dim := list_enum dim.
  
  (*Definition sum_fn (f : nat -> R) (l : list nat) : R := fold_right plusR zeroR (map f l). *) 
    
  Local Definition Cong := functional_matrix_congruence R eqR.
  
  (* generalised matrix multiplication 
  Definition matrix_mul_gen (m₁ m₂ : Matrix Node R) (l : list Node) : Matrix Node R :=
    fun (c d : Node) => sum_fn (fun y => (mulR(m₁ c y)(m₂ y d))) l.
   *)
  
  (* Specialised form of general multiplicaiton 
  Definition matrix_mul (m₁ m₂ : Matrix Node R) := matrix_mul_gen m₁ m₂ finN.


  Definition matrix_mul (m₁ m₂ : Matrix Node R) : Matrix Node R :=
    fun (i j : Node) => sum_fn (fun q => (mulR(m₁ i q)(m₂ q j))) finN finN.
  *)

                               
  Definition is_in_int_list a l := in_list brel_eq_nat l a = true.
  Definition not_in_int_list a l := in_list brel_eq_nat l a = false.
  Local Infix "[in]" := is_in_int_list (at level 70).
  Local Infix "[!in]" := not_in_int_list (at level 70).    

  Local Infix "+" := plusR.
  Local Infix "*" := mulR.
  Local Notation "0" := zeroR.
  Local Notation "1" := oneR.
  Local Notation "a =n= b" := (brel_eq_nat a b = true) (at level 70).
  Local Notation "a =r= b" := (eqR a b = true) (at level 70).
  Local Infix "=n?=" := brel_eq_nat (at level 70).
  Local Infix "=r?=" := eqR (at level 70).   
  Local Notation "a =l= b" := (brel_list brel_eq_nat a b = true) (at level 70).
  Local Notation "a +M b" := (matrix_add plusR a b) (at level 70).
  Local Notation "a *[ n ] b" := (matrix_mul 0 plusR mulR n a b) (at level 70).
  Local Notation "a =M= b" := (eq_functional_matrix_prop R eqR a b) (at level 70).

(* 
Variables 
    Semiring Axioms needed for associativity of *M 
    (plus_commutative  : bop_commutative R eqR plusR)
    (plus_associative : bop_associative R eqR plusR)
    (mul_associative : bop_associative R eqR mulR)
    (left_distributive_mul_over_plus : bop_left_distributive R eqR plusR mulR) 
    (right_distributive_mul_over_plus : bop_right_distributive R eqR plusR mulR)
    (plusID : bop_is_id R eqR plusR 0)
    (mulID : bop_is_id R eqR mulR 1)    
    (mulANN : bop_is_ann R eqR mulR 0).
*)


(*    
    Lemma sum_fn_mul_congr_diff : 
      ∀ l (e m₁ m₂ : Matrix Node R) c d, m₁ =M= m₂ ->
             sum_fn (λ y : Node, e c y * m₁ y d) l =r= sum_fn (λ y : Node, e c y * m₂ y d) l.
    Proof.
      induction l; simpl; 
      intros  ? ? ? ? ? Hm.
      + apply refR.
      + apply congrP. 
        apply congrM.
        apply refR.
        apply Hm.
        apply IHl; assumption.
    Qed.
 *)
    
    (* naming is very difficult. I can't come up meaningful names 
    Lemma mat_mul_cong_diff : 
      ∀ e m₁ m₂ c d, m₁ =M= m₂ -> (e *M m₁) c d =r= (e *M m₂) c d.
    Admitted.
     *)

    (* how about this? 
    Lemma matrix_multiplication_congruence_general : 
      ∀ m1 m2 ,  Cong m1 -> Cong m2 -> Cong (m1 *M m2). 
    Proof. intros m1 m2 A B a b c d C D.
           unfold matrix_mul. 
    Admitted.
*)     
    (* let's replace the above with a better congruence lemma 
    Lemma matrix_multiplication_congruence_general : 
      ∀ m1 m2 m3 m4,  Cong m1 -> Cong m2 -> Cong m3 -> Cong m4 -> 
        m1 =M= m2 -> m3 =M= m4 -> (m1 *M m3) =M= (m2 *M m4). 
    Admitted. 
    
*) 
(*
    Local Lemma rewrite_gen_ind : 
      ∀ a b c d e f g, 
        a * d + f =r= g -> a * (b * c + d) + (e * c + f) =r= (a * b + e) * c + g.
    Proof. 
      intros.
      assert (Ht : a * (b * c + d) + (e * c + f) =r= a * b * c + a * d + (e * c + f)).
      apply congrP.
      assert (Hw : a * b * c + a * d =r= a * (b * c) + a * d).
      apply congrP. apply mul_associative.
      apply refR. apply symR.
      rewrite <-Hw; clear Hw. 
      apply congrR. apply refR.
      apply left_distributive_mul_over_plus.
      apply refR.
      rewrite <-Ht; clear Ht. 
      apply congrR. 
      apply refR. apply symR.
      assert (Ht : a * b * c + a * d + (e * c + f) =r= a * b * c + (a * d + (e * c + f))).
      apply plus_associative.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      apply symR.
      assert (Ht : a * b * c + (a * d + (e * c + f)) =r= a * b * c + (e * c + a * d + f)).
      apply congrP. apply refR.
      assert (Hw : a * d + (e * c + f) =r= a * d + e * c + f).
      apply symR. apply plus_associative.
      rewrite <- Hw; clear Hw.
      apply congrR. apply refR.
      apply congrP. 
      apply plus_commutative.
      apply refR. 
      rewrite <- Ht; clear Ht.
      apply congrR.
      apply refR. apply symR.
      assert (Ht : (a * b + e) * c + g =r= a * b * c + e * c + g).
      apply congrP.
      apply right_distributive_mul_over_plus.
      apply refR. apply symR in Ht.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      assert (Ht : a * b * c + e * c + g =r= a * b * c + (e * c + g)).
      apply plus_associative. 
      apply symR in Ht.
      rewrite <- Ht; clear Ht.
      apply congrR. apply congrP.
      apply refR.
      assert (Ht : e * c + g =r= e * c + (a * d + f)).
      apply congrP. apply refR.
      apply symR. exact H.
      apply symR in Ht.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply plus_associative.
      all: apply refR.
    Qed.



Lemma matrix_mul_gen_assoc : 
      ∀ l₁ l₂ m₁ m₂ m₃ (c d : Node),
      (matrix_mul_gen Node R zeroR plusR mulR m₁ 
        (matrix_mul_gen Node R zeroR plusR mulR m₂ m₃ l₂) l₁ c d) =r= 
      (matrix_mul_gen Node R zeroR plusR mulR 
        (matrix_mul_gen Node R zeroR plusR mulR  m₁ m₂ l₁) m₃ l₂ c d) = true.

Definition mmg := matrix_mul_gen.
    
Lemma matrix_mul_gen_assoc : 
      ∀ l₁ l₂ m₁ m₂ m₃ (c d : Node), (mmg m₁ (mmg m₂ m₃ l₂) l₁) c d =r= (mmg (mmg m₁ m₂ l₁) m₃ l₂) c d.
    Proof.
      intros.
        revert l₁ l₂ m₁ m₂ m₃ c d.
      unfold mmg, matrix_mul_gen; induction l₁; simpl;
      intros ? ? ? ? ? ?. 
      +
        induction l₂; simpl.
        ++ apply refR.
        ++ destruct (mulANN (m₃ a d)) as [Ht _].
           assert (A := congrP _ _ _ _ Ht (symR _ _ IHl₂)). 
           destruct (plusID 0) as [B _].
           exact (symR _ _ (trnR _ _ _ A B)). 
      (* inductive case *)
      + specialize (IHl₁ l₂ m₁ m₂ m₃ c d).
        (* This one is going to be tricky *)
        assert (Ht: m₁ c a * sum_fn (λ y, m₂ a y * m₃ y d) l₂ +
                    sum_fn (λ y, m₁ c y * sum_fn (λ y0, m₂ y y0 * m₃ y0 d) l₂) l₁
                    =r=
                    m₁ c a * sum_fn (λ y, m₂ a y * m₃ y d) l₂ + 
                    sum_fn (λ y, sum_fn (λ y0, m₁ c y0 * m₂ y0 y) l₁ * m₃ y d) l₂).
        apply congrP.
        apply refR. 
        exact IHl₁.
        rewrite <-Ht.
        apply congrR. 
        apply refR.
        clear Ht; clear IHl₁.
        apply symR.
        induction l₂; simpl.
        ++ destruct (mulANN (m₁ c a)) as [_ A].
           destruct (plusID (m₁ c a * 0)) as [_ B].
           exact (trnR _ _ _ B A). 
        ++ apply rewrite_gen_ind. exact IHl₂.
    Qed.

 *)


  (* How about these distributive laws for sum_fn? *) 
  Lemma sum_fn_left_distributive
        (left_distributive_mul_over_plus : bop_left_distributive R eqR plusR mulR) 
        (mulANN : bop_is_ann R eqR mulR 0)
          (v : R) (f : nat -> R) (l : list nat) : v * (sum_fn zeroR plusR f l) =r= sum_fn zeroR plusR (fun h => v* (f h)) l.
  Proof. induction l.
         + compute. destruct (mulANN v) as [_ A]. exact A. 
         + unfold sum_fn. simpl. 
           assert (A := congrP _ _ _ _ (refR (v * f a)) IHl).
           assert (B := left_distributive_mul_over_plus v (f a) (sum_fn zeroR plusR f l)).            
           exact (trnR _ _ _ B A). 
  Qed.


  Lemma sum_fn_right_distributive
        (mulANN : bop_is_ann R eqR mulR 0)
        (right_distributive_mul_over_plus : bop_right_distributive R eqR plusR mulR)
        (v : R) (f : nat -> R) (l : list nat) : (sum_fn zeroR plusR f l) * v =r= sum_fn zeroR plusR (fun h => (f h) * v) l.
  Proof. induction l.
         + compute. destruct (mulANN v) as [A _]. exact A. 
         + unfold sum_fn. simpl. 
           assert (A := congrP _ _ _ _ (refR ((f a) * v)) IHl).
           assert (B := right_distributive_mul_over_plus v (f a) (sum_fn zeroR plusR f l)).            
           exact (trnR _ _ _ B A). 
  Qed.


  Lemma sum_fn_matrix_i_j_associative (l : list nat) : 
      ∀ m₁ m₂ m₃ i j, 
        sum_fn zeroR plusR (left_row_i_dot_col_j mulR m₁ (λ i0 j0 : nat, sum_fn zeroR plusR (left_row_i_dot_col_j mulR m₂ m₃ i0 j0) l) i j) l 
        =r=
        sum_fn zeroR plusR(left_row_i_dot_col_j mulR (λ i0 j0 : nat, sum_fn zeroR plusR (left_row_i_dot_col_j mulR m₁ m₂ i0 j0) l) m₃ i j) l. 
(*
  sum_fn (λ q : Node, m₁ i q * sum_fn (λ q0 : Node, m₂ q q0 * m₃ q0 j) finN) finN
  =r=
  sum_fn (λ q : Node, sum_fn (λ q0 : Node, m₁ i q * (m₂ q q0 * m₃ q0 j)) finN) finN
  =r=
  sum_fn (λ q : Node, sum_fn (λ q0 : Node, (m₁ i q * m₂ q q0) * m₃ q0 j) finN) finN
  =r=
  sum_fn (λ q0 : Node, sum_fn (λ q : Node, (m₁ i q * m₂ q q0) * m₃ q0 j) finN) finN
  =r=
  sum_fn (λ q : Node, sum_fn (λ q0 : Node, m₁ i q0 * m₂ q0 q) finN * m₃ q j) finN
*) 
Admitted. 
 


(*
    Lemma matrix_mul_assoc : 
      ∀ m₁ m₂ m₃ (c d : Node),
      matrix_mul Node finN R 0 plusR mulR m₁ 
        (matrix_mul Node finN R 0 plusR mulR m₂ m₃) c d =r= 
      matrix_mul Node finN R 0 plusR mulR 
        (matrix_mul Node finN R 0 plusR mulR m₁ m₂) m₃ c d = true.
*) 
    Lemma matrix_mul_associative (n : nat): 
      ∀ m₁ m₂ m₃, (m₁ *[n] (m₂ *[n] m₃)) =M= ((m₁ *[n] m₂) *[n] m₃).
    Proof. intros m₁ m₂ m₃ i j. 
           unfold matrix_mul. 
           apply sum_fn_matrix_i_j_associative; auto.
    Qed. 
           
    

(*            
    Lemma sum_fn_mul_distribute_over_plus_left: 
      ∀ (l : list Node) 
      (m₁ m₂ m₃ : Matrix Node R) (c d : Node),
        sum_fn (λ y, m₁ c y * (m₂ y d + m₃ y d)) l
         =r=
         sum_fn (λ y, m₁ c y * m₂ y d) l + sum_fn (λ y, m₁ c y * m₃ y d) l.
    Proof.
      induction l.
      - simpl. intros ? ? ? ? ?.
        destruct (plusID 0). exact (symR _ _ e). 
      - simpl; intros ? ? ? ? ?.
        pose proof (IHl m₁ m₂ m₃ c d) as IHt.
        remember (sum_fn (λ y, m₁ c y * (m₂ y d + m₃ y d)) l) as sfn₁.
        remember (sum_fn (λ y, m₁ c y * m₂ y d) l) as sfn₂.
        remember (sum_fn (λ y, m₁ c y * m₃ y d) l) as sfn₃.
        assert (Ht : (m₁ c a * (m₂ a d + m₃ a d) + sfn₁ =r?=
        m₁ c a * m₂ a d + sfn₂ + (m₁ c a * m₃ a d + sfn₃)) = 
        ((m₁ c a * m₂ a d + m₁ c a * m₃ a d) + (sfn₂ + sfn₃) =r?=
         m₁ c a * m₂ a d + sfn₂ + (m₁ c a * m₃ a d + sfn₃))).
        apply congrR.
        apply congrP.
        apply left_distributive_mul_over_plus.
        apply IHt.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht : 
        (m₁ c a * m₂ a d + m₁ c a * m₃ a d + (sfn₂ + sfn₃) =r?=
        m₁ c a * m₂ a d + sfn₂ + (m₁ c a * m₃ a d + sfn₃)) = 
        (m₁ c a * m₂ a d + (m₁ c a * m₃ a d + (sfn₂ + sfn₃)) =r?=
        m₁ c a * m₂ a d + sfn₂ + (m₁ c a * m₃ a d + sfn₃))).
        apply congrR.
        apply plus_associative.
        apply refR. 
        rewrite Ht; clear Ht.
        assert (Ht : 
        (m₁ c a * m₂ a d + (m₁ c a * m₃ a d + (sfn₂ + sfn₃)) =r?=
        m₁ c a * m₂ a d + sfn₂ + (m₁ c a * m₃ a d + sfn₃)) =
        (m₁ c a * m₂ a d + (m₁ c a * m₃ a d + (sfn₂ + sfn₃)) =r?=
        m₁ c a * m₂ a d + (sfn₂ + (m₁ c a * m₃ a d + sfn₃)))).
        apply congrR.
        apply refR.
        apply plus_associative.
        rewrite Ht; clear Ht.
        apply congrP.
        apply refR.
        assert (Ht : 
        (m₁ c a * m₃ a d + (sfn₂ + sfn₃) =r?= sfn₂ + (m₁ c a * m₃ a d + sfn₃)) = 
        (m₁ c a * m₃ a d + (sfn₂ + sfn₃) =r?= (m₁ c a * m₃ a d + sfn₃) + sfn₂)).
        apply congrR.
        apply refR.
        apply plus_commutative.
        rewrite Ht; clear Ht.
        assert (Ht: 
        (m₁ c a * m₃ a d + (sfn₂ + sfn₃) =r?= m₁ c a * m₃ a d + sfn₃ + sfn₂) =
        (m₁ c a * m₃ a d + (sfn₂ + sfn₃) =r?= m₁ c a * m₃ a d + (sfn₃ + sfn₂))).
        apply congrR. apply refR.
        apply plus_associative.
        rewrite Ht; clear Ht.
        apply congrP.
        apply refR.
        apply plus_commutative.
    Qed.
 *)

    Lemma sum_fn_left_distributes_over_matrix_i_j (l : list nat) : 
      ∀ m₁ m₂ m₃ i j,
        sum_fn zeroR plusR (left_row_i_dot_col_j mulR m₁ (λ c d : nat, m₂ c d + m₃ c d) i j) l 
        =r=
        sum_fn zeroR plusR (left_row_i_dot_col_j mulR m₁ m₂ i j) l + sum_fn zeroR plusR (left_row_i_dot_col_j mulR m₁ m₃ i j) l. 
    Admitted.    
    
    Lemma matrix_mul_left_distributive_over_matrix_add (n : nat) : 
      ∀ m₁ m₂ m₃, (m₁ *[n] (m₂ +M m₃)) =M= ((m₁ *[n] m₂) +M (m₁ *[n] m₃)).
    Proof. intros m₁ m₂ m₃ i j.
           unfold matrix_add, matrix_mul.
           apply sum_fn_left_distributes_over_matrix_i_j; auto.
    Qed. 

(*    
    Proof. intros m₁ m₂ m₃ a b. 
           unfold matrix_mul, matrix_mul_gen, matrix_add.
           apply sum_fn_mul_distribute_over_plus_left.
    Qed. 
    
    Lemma sum_fn_mul_distribute_over_plus_right : 
      ∀ (l : list Node) (m₁ m₂ m₃ : Matrix Node R) (c d : Node),
      (sum_fn (λ y, (m₂ c y + m₃ c y) * m₁ y d) l =r=
      sum_fn (λ y, m₂ c y * m₁ y d) l + sum_fn (λ y, m₃ c y * m₁ y d) l).
    Proof.
      induction l.
      - simpl. intros ? ? ? ? ?.
        destruct (plusID 0) as [A _]. 
        apply symR. exact A. 
      - simpl; intros ? ? ? ? ?.
        pose proof (IHl m₁ m₂ m₃ c d) as IHt.
        remember (sum_fn (λ y, (m₂ c y + m₃ c y) * m₁ y d) l) as sfn₁.
        remember (sum_fn (λ y, m₂ c y * m₁ y d) l) as sfn₂.
        remember (sum_fn (λ y, m₃ c y * m₁ y d) l) as sfn₃.
        assert (Ht: 
        ((m₂ c a + m₃ c a) * m₁ a d + sfn₁ =r?=
        m₂ c a * m₁ a d + sfn₂ + (m₃ c a * m₁ a d + sfn₃)) =
        ((m₂ c a * m₁ a d + m₃ c a * m₁ a d) + (sfn₂ + sfn₃) =r?=
        m₂ c a * m₁ a d + sfn₂ + (m₃ c a * m₁ a d + sfn₃))).
        apply congrR.
        apply congrP.
        apply right_distributive_mul_over_plus.
        exact IHt.
        apply refR.
        rewrite Ht; clear Ht.
        assert(Ht: 
        (m₂ c a * m₁ a d + m₃ c a * m₁ a d + (sfn₂ + sfn₃) =r?=
        m₂ c a * m₁ a d + sfn₂ + (m₃ c a * m₁ a d + sfn₃)) =
        (m₂ c a * m₁ a d + (m₃ c a * m₁ a d + (sfn₂ + sfn₃)) =r?=
        m₂ c a * m₁ a d + (sfn₂ + (m₃ c a * m₁ a d + sfn₃)))).
        apply congrR.
        apply plus_associative.
        apply plus_associative.
        rewrite Ht; clear Ht.
        apply congrP.
        apply refR.
        assert (Ht : 
        (m₃ c a * m₁ a d + (sfn₂ + sfn₃) =r?= sfn₂ + (m₃ c a * m₁ a d + sfn₃)) = 
        (m₃ c a * m₁ a d + (sfn₂ + sfn₃) =r?= (m₃ c a * m₁ a d + sfn₃) + sfn₂)).
        apply congrR.
        apply refR.
        apply plus_commutative.
        rewrite Ht; clear Ht.
        assert (Ht: 
        (m₃ c a * m₁ a d + (sfn₂ + sfn₃) =r?= m₃ c a * m₁ a d + sfn₃ + sfn₂) =
        (m₃ c a * m₁ a d + (sfn₂ + sfn₃) =r?= m₃ c a * m₁ a d + (sfn₃ + sfn₂))).
        apply congrR. apply refR.
        apply plus_associative.
        rewrite Ht; clear Ht.
        apply congrP.
        apply refR.
        apply plus_commutative.
    Qed.
    
 *)
    Lemma sum_fn_right_distributes_over_matrix_i_j (l : list nat) : 
      ∀ m₁ m₂ m₃ i j, 
         sum_fn zeroR plusR (left_row_i_dot_col_j mulR (λ c d : nat, m₂ c d + m₃ c d) m₁ i j) l 
         =r=
         sum_fn zeroR plusR (left_row_i_dot_col_j mulR m₂ m₁ i j) l + sum_fn zeroR plusR (left_row_i_dot_col_j mulR m₃ m₁ i j) l.
    Admitted.
    
    Lemma matrix_mul_right_distributes_over_matrix_add (n : nat): 
      ∀ m₁ m₂ m₃, ((m₂ +M m₃) *[n] m₁) =M= ((m₂ *[n] m₁) +M (m₃ *[n] m₁)).
    Proof. intros m₁ m₂ m₃ i j.
           unfold matrix_add, matrix_mul.
           apply sum_fn_right_distributes_over_matrix_i_j; auto.
    Qed. 

    (****************** mulitplicative idenitity matrix ***************************)



  Definition I := matrix_mul_identity 0 1. 

  (* I * m =M= m. 
   proof:
    (I *m) i j 
    = sum_fn (fun q => (mulR(I i q)(m q j))) finN. 
    = sum_fn (fun q => (mulR(if i =n? q then 1 else 0)())) finN. 
    = sum_fn (fun q => (if i =n? q then m q j else 0)) finN. 
    = m i j 
   *)

  Lemma matrix_i_j_left_identity :
    ∀ m i j q, ((fun q => left_row_i_dot_col_j mulR I m i j q) q) =r= (fun _ => if i =n?= j then m i j else 0) q. 
  Admitted.         

  Lemma matrix_mul_I_is_left_identity (n : nat) : ∀ m, I *[n] m =M= m.
  Proof. intros m i j. unfold matrix_mul. 
         induction n; unfold domain. 
  Admitted.

  Lemma matrix_mul_I_is_right_identity (n : nat) : ∀ m, m *[n] I =M= m.
           
  Admitted.


  Lemma matrix_mul_I_is_identity (n : nat) : ∀ m, (I *[n] m =M= m) /\ (m *[n] I =M= m).
  Proof. intros m. split. 
         + apply matrix_mul_I_is_left_identity; auto.
         + apply matrix_mul_I_is_right_identity; auto.           
  Qed.

  Lemma matrix_mul_identity_congruence : Cong I. 
  Admitted.

  
  
(*  
    Lemma identity_cong : Cong I. 
    Proof. 
      intros a b c d Hac Hbd. unfold I. 
      case_eq (a =n?= b); intros Hf; auto.
      assert (Ht1 := trnN _ _ _ Hf Hbd).
      apply symN in Hac.
      assert (Ht2 := trnN _ _ _ Hac Ht1).
      rewrite Ht2. 
      apply refR.
      case_eq (c =n?= d); intros Hcd; auto.
      assert (Had := trnN _ _ _ Hac Hcd).
      apply symN in Hbd.
      assert (Habt := trnN _ _ _ Had Hbd).
      rewrite Habt in Hf.
      inversion Hf.
    Qed.
*) 

(*
    Lemma sum_fn_list_app : 
      ∀ (l₁ l₂ : list Node) (f : Node -> R), 
      sum_fn  f (l₁ ++ l₂) =r= (sum_fn f l₁ + sum_fn f l₂).
    Proof. 
      induction l₁; simpl.
      intros ? ?.
      + destruct (plusID (sum_fn f l₂)) as [A _ ]. exact (symR _ _ A). 
      + intros ? ?.
        specialize (IHl₁ l₂ f).
        assert (Ht : f a + sum_fn f l₁ + sum_fn f l₂
                     =r= 
                    f a + (sum_fn f l₁ + sum_fn f l₂)).
        apply plus_associative.
        apply symR in Ht.
        rewrite <-Ht; clear Ht.
        apply congrR. 
        apply congrP.
        apply refR. 
        exact IHl₁.
        apply refR.
    Qed.


    
    Lemma sum_fn_three_list_app : 
      ∀ (l₁ l₂ l₃ : list Node) (f : Node -> R), 
         sum_fn f (l₁ ++ l₂ ++ l₃) =r= sum_fn f l₁ + sum_fn f l₂ + sum_fn f l₃.
    Proof.
      intros. 
      assert (Ht : sum_fn f (l₁ ++ l₂ ++ l₃) =r= sum_fn f l₁ + sum_fn f (l₂ ++ l₃)).
      apply sum_fn_list_app. 
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      assert (Ht: sum_fn f l₁ + sum_fn f l₂ + sum_fn f l₃
                  =r= 
                 sum_fn f l₁ + (sum_fn f l₂ + sum_fn f l₃)).
      apply plus_associative.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply congrP. 
      apply refR.
      apply sum_fn_list_app.
    Qed.

    Lemma sum_fn_list_eqv_gen : ∀  (l la lb : list Node) (f : Node -> R), 
       fncong f -> l =l= (la ++ lb)-> sum_fn f l =r= sum_fn f (la ++ lb).
    Proof.
      induction l.
      + simpl; intros ? ? ? Hc Hl.
        destruct (la ++ lb).
        simpl. 
        apply refR.
        inversion Hl.
      + intros ? ? ? Hc Hl. 
        destruct la; destruct lb.
        - inversion Hl.
        - simpl in * |- *.
          apply Bool.andb_true_iff in Hl.
          destruct Hl as [Hla Hlb].
          specialize (IHl [] lb f Hc Hlb).
          simpl in IHl. 
          apply congrP.
          apply Hc. 
          exact Hla.
          exact IHl.
        - simpl in * |- *.
          apply Bool.andb_true_iff in Hl.
          destruct Hl as [Hla Hlb].
          apply congrP.
          apply Hc. 
          exact Hla.
          specialize (IHl la [] f Hc Hlb).
          exact IHl.
        - simpl in * |- *.
          apply Bool.andb_true_iff in Hl.
          destruct Hl as [Hla Hlb].
          specialize(IHl la (n0 :: lb) f Hc Hlb).
          apply congrP.
          apply Hc. 
          exact Hla.
          exact IHl.
    Qed.

    Lemma sum_fn_list_eqv : 
      ∀ (l la lb : list Node) (c : Node) (f : Node -> R), 
      fncong f -> l =l= (la ++ [c] ++ lb)-> sum_fn f l =r= sum_fn f (la ++ [c] ++ lb).
    Proof. intros ? ? ? ? ? Hc Hl. exact (sum_fn_list_eqv_gen l la ([c] ++ lb) f Hc Hl). Qed. 
*) 
(*    
    Lemma sum_fn_not_mem : 
      ∀ (l : list Node) (c d : Node) 
      (m : Node -> Node -> R),  in_list eqN l c = false ->
      sum_fn (λ y : Node, (if c =n?= y then 1 else 0) * m y d) l =r= 0.
    Proof.
      induction l; simpl; intros c d m H.
      + apply refR.
      + apply Bool.orb_false_iff in H.
        destruct H as [Ha Hb]. 
        rewrite Ha.
        specialize (IHl c d m Hb).
        assert (Ht : 0 * m a d + 
          sum_fn (λ y : Node, (if c =n?= y then 1 else 0) * m y d) l =r= 
          0 + sum_fn (λ y : Node, (if c =n?= y then 1 else 0) * m y d) l 
         ).
        apply congrP. 
        destruct (mulANN (m a d)) as [A _]. exact A.
        apply refR.        
        rewrite <-IHl. 
        apply congrR.
        destruct (plusID (sum_fn (λ y : Node, (if c =n?= y then 1 else 0) * m y d) l)) as [A _].
        exact (trnR _ _ _ Ht A).
        apply refR. 
    Qed.


    Lemma sum_fn_not_mem_dnode : 
      ∀ (l : list Node) (c d : Node)  (m : Node -> Node -> R), 
         d [!in] l -> sum_fn (λ y, m c y * (if y =n?= d then 1 else 0)) l =r= 0.
    Proof.
      induction l; simpl; intros c d m H.
      + apply refR.
      + apply Bool.orb_false_iff in H.
        destruct H as [Ha Hb].
        assert (a =n?= d = false).
        case_eq (a =n?= d); intro Hf; auto.
        apply symN in Hf.
        rewrite Hf in Ha.
        inversion Ha.
        rewrite H.
        assert (Ht : 
          m c a * 0 +
          sum_fn (λ y : Node, m c y * (if y =n?= d then 1 else 0)) l =r= 
          m c a * 0 + 0).
        apply congrP. 
        apply refR.
        specialize (IHl c d m Hb).
        exact IHl.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply congrP. 
        apply refR.
        apply refR.
        apply symR.
        assert (Ht : m c a * 0 + 0 =r= m c a * 0).
           destruct (plusID (m c a * 0)) as [_ A]; exact A. 
        rewrite <-Ht; clear Ht.
        apply congrR. 
        apply refR.
        apply symR.
        destruct (mulANN (m c a)) as [_ A]; exact A. 
    Qed.

     
      Lemma matrix_mul_left_identity_gen : 
        ∀ (l : list Node),
          l <> [] ->
          (∀ x : Node, in_list eqN l x = true) -> 
          no_dup Node eqN l = true-> 
            ∀ (m : Matrix Node R) (c d : Node),  Cong m -> (mmg I m l) c d =r= m c d. 
    Proof.
      unfold matrix_mul_gen, I, Cong.
      intros ? Hl Hx Hn ? ? ? Hm.
      destruct (list_split _ eqN refN symN trnN l c Hl (Hx c) 
        Hn) as [la [lb [Hleq [Hina Hinb]]]].
      assert (Ht : 
        sum_fn 
          (λ y : Node, (if c =n?= y then 1 else 0) * m y d) l =r= 
        sum_fn 
          (λ y : Node, (if c =n?= y then 1 else 0) * m y d) (la ++ [c] ++ lb)
       ).
      apply sum_fn_list_eqv.
      unfold fncong.
      intros.
      destruct (c =n?= a) eqn:Ht.
      pose proof (trnN _ _ _ Ht H) as Hcb.
      rewrite Hcb. 
      destruct (mulID (m a d)) as [Htt _]. 
      rewrite <-Htt; clear Htt. 
      apply congrR.
      apply refR.
      destruct (mulID (m b d)) as [Htt _]. 
      rewrite <-Htt; clear Htt.
      apply congrR. 
      apply refR.
      apply Hm. 
      exact H.
      apply refN.
      case_eq (c =n?= b); intros Hf; auto.
      apply symN in H.
      assert (Htt := trnN _ _ _ Hf H).
      rewrite Ht in Htt.
      inversion Htt.

      exact Hleq. 
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR. 
      assert (Ht : 
        sum_fn
        (λ y : Node, (if c =n?= y then 1 else 0) * m y d) (la ++ [c] ++ lb)
        =r= 
        sum_fn (λ y : Node, (if c =n?= y then 1 else 0) * m y d) la + 
        sum_fn (λ y : Node, (if c =n?= y then 1 else 0) * m y d) [c] + 
        sum_fn (λ y : Node, (if c =n?= y then 1 else 0) * m y d) lb).
      apply sum_fn_three_list_app.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      simpl. 
      assert (Hc : c =n= c).
      apply refN. 
      rewrite Hc; clear Hc.
      apply symR.
      assert (Ht : 
        sum_fn
        (λ y : Node, (if c =n?= y then 1 else 0) * m y d) la + 
        (1 * m c d + 0) +
        sum_fn
        (λ y : Node, (if c =n?= y then 1 else 0) * m y d) lb =r= 
        0 + (1 * m c d + 0) + 0).
      apply congrP. 
      apply congrP.
      apply sum_fn_not_mem. 
      exact Hina.
      apply refR.
      apply sum_fn_not_mem. 
      exact Hinb.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR.
      assert (Ht : 0 + (1 * m c d + 0) + 0 =r= 0 + (1 * m c d + 0)).
         destruct (plusID (0 + (1 * m c d + 0))) as [_ A]; exact A. 
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR. 
      assert (Ht: 0 + (1 * m c d + 0) =r= (1 * m c d + 0)).
         destruct (plusID (1 * m c d + 0)) as [A _]; exact A. 
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      apply symR.
      assert (Ht : 1 * m c d + 0 =r= 1 * m c d).
         destruct (plusID (1 * m c d)) as [_ A]; exact A. 
      rewrite <-Ht; 
      clear Ht. 
      apply congrR.
      apply refR.
      apply symR.
      destruct (mulID (m c d)) as [A _]; exact A. 
    Qed.


    
    
    Lemma matrix_mul_right_identity_gen : 
      ∀ (l : list Node),
      l <> [] -> 
      (∀ x : Node, in_list eqN l x = true) -> 
      no_dup Node eqN l = true -> 
      ∀ (m : Matrix Node R ),  Cong m -> (mmg m I l) =M= m. 
    Proof. 
      unfold matrix_mul_gen, I.
      intros l Hl Hx Hn m cong c d. 
      destruct (list_split _ eqN refN symN trnN l d Hl (Hx d) Hn) as [la [lb [Hleq [Hina Hinb]]]].
      assert (Ht : 
        sum_fn 
          (λ y : Node, m c y * (if y =n?= d then 1 else 0)) l =r= 
        sum_fn
          (λ y : Node, m c y * (if y =n?= d then 1 else 0)) (la ++ [d] ++ lb)
       ).
      apply sum_fn_list_eqv.
      unfold fncong.
      intros.
      destruct (a =n?= d) eqn:Ht.
      apply symN in H.
      pose proof (trnN _ _ _ H Ht) as Hbd.
      rewrite Hbd.
      assert (Htt : m c a * 1 =r= m c a).
         destruct (mulID (m c a)) as [_ A]; exact A. 
      rewrite <-Htt; clear Htt. 
      apply congrR.
      apply refR.
      assert (Htt : m c b * 1 =r= m c b).
         destruct (mulID (m c b)) as [_ A]; exact A. 
      rewrite <-Htt; clear Htt.
      apply congrR. 
      apply refR.
      apply cong. 
      apply refN. 
      apply symN in H. 
      exact H.
      case_eq (b =n?= d); intros Hf; auto.
      assert (Htt := trnN _ _ _ H Hf).
      rewrite Ht in Htt.
      inversion Htt.
      exact Hleq. 
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR.
      assert (Ht : 
        sum_fn (λ y : Node, m c y * (if y =n?= d then 1 else 0)) (la ++ [d] ++ lb)
        =r= 
        sum_fn (λ y : Node, m c y * (if y =n?= d then 1 else 0)) la + 
        sum_fn (λ y : Node, m c y * (if y =n?= d then 1 else 0)) [d] + 
        sum_fn (λ y : Node, m c y * (if y =n?= d then 1 else 0)) lb).
      apply sum_fn_three_list_app.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      simpl. 
      assert (Hd : d =n= d).
      apply refN. 
      rewrite Hd; clear Hd.
      assert (Ht :
        sum_fn (λ y : Node, m c y * (if y =n?= d then 1 else 0)) la +
        (m c d * 1 + 0) +
        sum_fn (λ y : Node, m c y * (if y =n?= d then 1 else 0)) lb =r= 
        0 + (m c d * 1 + 0) + 0).
      apply congrP. 
      apply congrP.
      apply sum_fn_not_mem_dnode. 
      exact Hina.
      apply refR.
      apply sum_fn_not_mem_dnode. 
      exact Hinb.
      apply symR.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR.
      assert (Ht : 0 + (m c d * 1 + 0) + 0 =r= 0 + (m c d * 1 + 0) ).
         destruct (plusID (0 + (m c d * 1 + 0))) as [_ A]; exact A. 
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR.
      assert (Ht: 0 + (m c d * 1 + 0) =r= (m c d * 1 + 0)).
         destruct (plusID (m c d * 1 + 0)) as [A _]; exact A.       
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      apply symR.
      assert (Ht : m c d * 1 + 0 =r= m c d * 1).
         destruct (plusID (m c d * 1)) as [_ A]; exact A.          
      rewrite <-Ht; 
      clear Ht. 
      apply congrR. 
      apply refR.
      apply symR. 
      destruct (mulID (m c d)) as [_ A]; exact A.          
    Qed.

    
*) 
    
End Matrix_Multiplication.   
