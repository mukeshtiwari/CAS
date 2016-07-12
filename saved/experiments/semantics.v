
Definition annotated_eqv_base_sem (b : te_base) : AnnotatedEQV (te_to_Type (te_from_base b)) :=
  match b with 
  | te_bool    => annotated_brel_eq_bool 
  | te_num Nat => annotated_brel_eq_nat 
  end. 


Fixpoint eqv_annotated_sem (t : te) (x : tEQV t) : AnnotatedEQV (te_to_Type t) :=
   match x in tEQV t return  AnnotatedEQV (te_to_Type t) with
   | eqvBase          b => annotated_eqv_base_sem b
   | eqvList        s x => annotated_brel_list (te_to_Type s) (eqv_annotated_sem s x)
   | eqvSet         s x => annotated_brel_set (te_to_Type s) (eqv_annotated_sem s x)
   | eqvSum     s t x y => annotated_brel_sum (te_to_Type s) (te_to_Type t) (eqv_annotated_sem s x) (eqv_annotated_sem t y)
   | eqvProduct s t x y => annotated_brel_product (te_to_Type s) (te_to_Type t) (eqv_annotated_sem s x) (eqv_annotated_sem t y)
   end. 


Fixpoint sg_annotated_sem (t : te) (x : tSG t) : AnnotatedSemigroup (te_to_Type t) :=
   match x with
   | stAnd                => annotated_semigroup_and 
   | stOr                 => annotated_semigroup_or
   | stMin Nat            => annotated_semigroup_min 
   | stMax Nat            => annotated_semigroup_max 
   | stPlus Nat           => annotated_semigroup_plus 
   | stTimes Nat          => annotated_semigroup_times 
   | stLeftSum s t x y    => 
        annotated_semigroup_left_sum (te_to_Type s) (te_to_Type t) (sg_annotated_sem s x) (sg_annotated_sem t y)
   | stRightSum s t  x y   => 
        annotated_semigroup_right_sum (te_to_Type s) (te_to_Type t) (sg_annotated_sem s x) (sg_annotated_sem t y)
   | stProduct s t  x y    => 
        annotated_semigroup_product (te_to_Type s) (te_to_Type t) (sg_annotated_sem s x) (sg_annotated_sem t y)
   | stLeft s x  => annotated_semigroup_left (te_to_Type s)  (eqv_annotated_sem s x) 
   | stRight s x => annotated_semigroup_right (te_to_Type s)  (eqv_annotated_sem s x) 
   | stConcat s x => annotated_semigroup_concat (te_to_Type s)  (eqv_annotated_sem s x) 
   | stUnion s x => annotated_semigroup_union (te_to_Type s)  (eqv_annotated_sem s x) 
   end. 

Fixpoint pos_annotated_sem (t : te) (x : tPOS t) : option (AnnotatedPartialOrder (te_to_Type t)) :=
   match x with
   | tposFromSemigroupLeft t x  => 
        annotated_pos_left_from_sgr (te_to_Type t) (sg_annotated_sem t x) 
   | tposFromSemigroupRight t x => 
        annotated_pos_right_from_sgr (te_to_Type t) (sg_annotated_sem t x) 
   end. 


Definition eqv_checked_base_sem (b : te_base) : CheckedEQV (te_to_Type (te_from_base b)) :=
  match b with 
  | te_bool    => (brel_eq_bool, {| eqv_check_not_trivial := CheckNotTrivial bool true false |})
  | te_num Nat => (brel_eq_nat, {| eqv_check_not_trivial := CheckNotTrivial nat 0 1 |})
  end. 

Fixpoint eqv_checked_sem (t : te) (x : tEQV t) : CheckedEQV (te_to_Type t) :=
   match x in tEQV t return CheckedEQV (te_to_Type t) with
   | eqvBase          b => eqv_checked_base_sem b
   | eqvList        s x => eqv_checked_list (te_to_Type s) (eqv_checked_sem s x)
   | eqvSet         s x => eqv_checked_set (te_to_Type s) (eqv_checked_sem s x)
   | eqvSum     s t x y => eqv_checked_sum (te_to_Type s) (te_to_Type t) (eqv_checked_sem s x) (eqv_checked_sem t y)
   | eqvProduct s t x y => eqv_checked_product (te_to_Type s) (te_to_Type t) (eqv_checked_sem s x) (eqv_checked_sem t y)
   end. 

Fixpoint sg_checked_sem (t : te) (x : tSG t) : CheckedSemigroup (te_to_Type t) :=
   match x in tSG t return CheckedSemigroup (te_to_Type t) with
   | stAnd                => checked_bool_and 
   | stOr                 => checked_bool_or
   | stMin Nat            => checked_nat_min 
   | stMax Nat            => checked_nat_max 
   | stPlus Nat           => checked_nat_plus 
   | stTimes Nat          => checked_nat_times 
   | stLeft s x           => checked_semigroup_left (te_to_Type s) (eqv_checked_sem s x)
   | stRight s x          => checked_semigroup_right (te_to_Type s) (eqv_checked_sem s x)
   | stConcat s x         => checked_semigroup_concat (te_to_Type s) (eqv_checked_sem s x)
   | stUnion s x          => checked_semigroup_union (te_to_Type s) (eqv_checked_sem s x)
   | stLeftSum s t x y    => 
        checked_semigroup_left_sum (te_to_Type s) (te_to_Type t) (sg_checked_sem s x) (sg_checked_sem t y)
   | stRightSum s t  x y   => 
        checked_semigroup_right_sum (te_to_Type s) (te_to_Type t) (sg_checked_sem s x) (sg_checked_sem t y)
   | stProduct s t  x y    => 
        checked_semigroup_product (te_to_Type s) (te_to_Type t) (sg_checked_sem s x) (sg_checked_sem t y)
   end. 


(* ******************** Main Theorem *************************** 

SHOW>> ∀ a, f a = g (h a) 
by induction on a. 

Here : 
f = sg_checked_sem 
h = sg_annotated_sem
g = annotated_semigroup_to_checked_semigroup 


General induction step: 

H1 : f a = g (h a) 
H2 : f b = g (h b) 
f (C a b) = c1 (f a) (f b)       
h (C a b) = c2 (h a) (h b)

SHOW>> c1 (f a) (f b) = g (c2 (h a) (h b)) 

Method 1: 

SHOW>> c1 (g (h a)) (g (h b)) = g (c2 (h a) (h b)) 

Lemma_c1_c2 : ∀ m n, c1 (g m) (g n) = g (c2 m n) 

Example: C === (stLeftSum s t) 
         c1 ===   checked_semigroup_left_sum (te_to_Type s) (te_to_Type t)
         c2 === annotated_semigroup_left_sum (te_to_Type s) (te_to_Type t)

Lemma  checked_annotated_left_sum: 
    ∀ s t : te,  ∀ aS : AnnotatedSemigroup (te_to_Type s), ∀ aT : AnnotatedSemigroup (te_to_Type t), 
      checked_semigroup_left_sum 
           (te_to_Type s) 
           (te_to_Type t) 
           (annotated_semigroup_to_checked_semigroup _ aS)
           (annotated_semigroup_to_checked_semigroup _ aT)
      = annotated_semigroup_to_checked_semigroup _ 
          (annotated_semigroup_left_sum (te_to_Type s) (te_to_Type t) aS aT)
.
*)


Definition annotated_eqv_to_checked_eqv : ∀ (S : Type), AnnotatedEQV S -> CheckedEQV S 
:= λ S aE,  
    match eqv_not_trivial _ _ (projT2 aE) with 
    | existT s (existT t _) => (projT1 aE, {| eqv_check_not_trivial := CheckNotTrivial S s t |} )
    end. 

Lemma correct_eqv_checked_list : ∀ S : Type, ∀ eS : AnnotatedEQV S, 
   eqv_checked_list S (annotated_eqv_to_checked_eqv S eS) 
   =
   annotated_eqv_to_checked_eqv (list S) (annotated_brel_list S eS). 
Proof. intros S eS. destruct eS. destruct e. 
       destruct eqv_not_trivial0 as [s [t P]]. 
       unfold annotated_brel_list. simpl. 
       unfold annotated_eqv_to_checked_eqv.  simpl. 
       unfold eqv_checked_list.
       unfold eqv_check_not_trivial. simpl. reflexivity. 
Defined. 

Lemma correct_eqv_checked_set : ∀ S : Type, ∀ eS : AnnotatedEQV S, 
   eqv_checked_set S (annotated_eqv_to_checked_eqv S eS) 
   =
   annotated_eqv_to_checked_eqv (list S) (annotated_brel_set S eS). 
Proof. intros S eS. destruct eS. destruct e. 
       destruct eqv_not_trivial0 as [s [t P]]. 
       unfold annotated_brel_set. simpl. 
       unfold annotated_eqv_to_checked_eqv.  simpl. 
       unfold eqv_checked_set.
       unfold eqv_check_not_trivial. simpl. reflexivity. 
Defined. 

Lemma correct_eqv_checked_product : ∀ S T : Type, ∀ eS : AnnotatedEQV S, ∀ eT : AnnotatedEQV T, 
   eqv_checked_product S T (annotated_eqv_to_checked_eqv S eS) (annotated_eqv_to_checked_eqv T eT) 
   = 
   annotated_eqv_to_checked_eqv (S * T) (annotated_brel_product S T eS eT). 
Proof. intros S T eS eT. destruct eS. destruct eT. destruct e. destruct e0. 
       destruct eqv_not_trivial0 as [s1 [s2 PS]]. 
       destruct eqv_not_trivial1 as [t1 [t2 PT]]. 
       unfold annotated_brel_product. simpl. 
       unfold annotated_eqv_to_checked_eqv.  simpl. 
       unfold eqv_checked_product.
       unfold eqv_check_not_trivial. simpl. reflexivity. 
Defined. 

Lemma correct_eqv_checked_sum : ∀ S T : Type, ∀ eS : AnnotatedEQV S, ∀ eT : AnnotatedEQV T, 
   eqv_checked_sum S T (annotated_eqv_to_checked_eqv S eS) (annotated_eqv_to_checked_eqv T eT) 
   = 
   annotated_eqv_to_checked_eqv (S + T) (annotated_brel_sum S T eS eT). 
Proof. intros S T eS eT. destruct eS. destruct eT. destruct e. destruct e0. 
       destruct eqv_not_trivial0 as [s1 [s2 PS]]. 
       destruct eqv_not_trivial1 as [t1 [t2 PT]]. 
       unfold annotated_brel_sum. simpl. 
       unfold annotated_eqv_to_checked_eqv.  simpl. 
       unfold eqv_checked_sum.
       unfold eqv_check_not_trivial. simpl. reflexivity. 
Defined. 

Theorem eqv_checked_sem_correct : 
        ∀ t : te,  ∀ e : tEQV t, eqv_checked_sem t e 
                                = annotated_eqv_to_checked_eqv (te_to_Type t) 
                                   (eqv_annotated_sem t e). 
Proof.  intro t. induction e; simpl. 
        destruct b. 
           reflexivity. 
           destruct n. reflexivity. 
        rewrite IHe. apply correct_eqv_checked_list. 
        rewrite IHe. apply correct_eqv_checked_set. 
        rewrite IHe1, IHe2. apply correct_eqv_checked_product. 
        rewrite IHe1, IHe2. apply correct_eqv_checked_sum.         
Defined. 

Lemma  annotated_semigroup_product_projT1 : 
    ∀ S T : Type,  ∀ aS : AnnotatedSemigroup S, ∀ aT : AnnotatedSemigroup T, 
     (semigroup_product S T (projT1 aS) (projT1 aT))
   =  (projT1 (annotated_semigroup_product S T aS aT)). 
Proof. intros S T aS aT. 
       unfold annotated_semigroup_product. 
       unfold projT1 at 3. reflexivity. 
Defined.  

Lemma  annotated_semigroup_left_sum_projT1 : 
    ∀ S T : Type,  ∀ aS : AnnotatedSemigroup S, ∀ aT : AnnotatedSemigroup T, 
     (semigroup_left_sum S T (projT1 aS) (projT1 aT))
   =  (projT1 (annotated_semigroup_left_sum S T aS aT)). 
Proof. intros S T aS aT. 
       unfold annotated_semigroup_left_sum. 
       destruct aS; destruct aT. 
       destruct s; destruct s0. 
       destruct sg_equiv0; destruct sg_equiv1.
       unfold eqv_not_trivial. 
       unfold projT1 at 1. 
       unfold projT1 at 1. 
       unfold projT1 at 1. 
       destruct eqv_not_trivial0 as [s1 [s2 pS]]; destruct eqv_not_trivial1 as [t1 [t2 pT]];
       reflexivity. 
Defined.  


Lemma  annotated_semigroup_right_sum_projT1 : 
    ∀ S T : Type,  ∀ aS : AnnotatedSemigroup S, ∀ aT : AnnotatedSemigroup T, 
     (semigroup_right_sum S T (projT1 aS) (projT1 aT))
   =  (projT1 (annotated_semigroup_right_sum S T aS aT)). 
Proof. intros S T aS aT. 
       unfold annotated_semigroup_right_sum. 
       destruct aS; destruct aT. 
       destruct s; destruct s0. 
       destruct sg_equiv0; destruct sg_equiv1.
       unfold eqv_not_trivial. 
       unfold projT1 at 1. 
       unfold projT1 at 1. 
       unfold projT1 at 1. 
       destruct eqv_not_trivial0 as [s1 [s2 pS]]; destruct eqv_not_trivial1 as [t1 [t2 pT]];
       reflexivity. 
Defined.  

Lemma checked_annotated_product : 
    ∀ S T : Type,  ∀ aS : AnnotatedSemigroup S, ∀ aT : AnnotatedSemigroup T, 
      checked_semigroup_product S T 
           (annotated_semigroup_to_checked_semigroup S aS)
           (annotated_semigroup_to_checked_semigroup T aT)
      = annotated_semigroup_to_checked_semigroup _ 
          (annotated_semigroup_product S T aS aT). 
Proof. 
   intros S T aS aT. 
   (* unwind RHS *) 
   unfold annotated_semigroup_to_checked_semigroup at 3. 
   unfold semigroup_proofs_to_checks. 
(*    rewrite (rewrite_test S T aS aT). *) 

   (* unwind LHS *) 
   unfold annotated_semigroup_to_checked_semigroup. 
   unfold checked_semigroup_product. 
   unfold fst, snd. 

   (* rewrite LHS to become RHS *) 
   rewrite (annotated_semigroup_product_projT1 S T aS aT) at 1. 
   rewrite (correct_checked_semigroup_product_commutative S T aS aT). 
   rewrite (correct_checked_semigroup_product_selective S T aS aT). 
   rewrite (correct_checked_semigroup_product_is_left S T aS aT). 
   rewrite (correct_checked_semigroup_product_is_right S T aS aT). 
   rewrite (correct_checked_semigroup_product_idempotent S T aS aT). 
   rewrite (correct_checked_semigroup_product_not_trivial S T aS aT). 
   reflexivity. 
Defined. 


Lemma checked_annotated_left_sum: 
    ∀ S T : Type,  ∀ aS : AnnotatedSemigroup S, ∀ aT : AnnotatedSemigroup T, 
      checked_semigroup_left_sum S T 
           (annotated_semigroup_to_checked_semigroup S aS)
           (annotated_semigroup_to_checked_semigroup T aT)
      = annotated_semigroup_to_checked_semigroup _ 
          (annotated_semigroup_left_sum S T aS aT). 
Proof. 
   intros S T aS aT. 
   (* unwind RHS *) 
   unfold annotated_semigroup_to_checked_semigroup at 3. 
   unfold semigroup_proofs_to_checks. 
(*    rewrite (rewrite_test S T aS aT). *) 

   (* unwind LHS *) 
   unfold annotated_semigroup_to_checked_semigroup. 
   unfold checked_semigroup_left_sum. 
   unfold fst, snd. 

   (* rewrite LHS to become RHS *) 
   rewrite (annotated_semigroup_left_sum_projT1 S T aS aT) at 1. 
   rewrite (correct_checked_semigroup_left_sum_commutative S T aS aT). 
   rewrite (correct_checked_semigroup_left_sum_selective S T aS aT). 
   rewrite (correct_checked_semigroup_left_sum_is_left S T aS aT). 
   rewrite (correct_checked_semigroup_left_sum_is_right S T aS aT). 
   rewrite (correct_checked_semigroup_left_sum_idempotent S T aS aT). 
   rewrite (correct_checked_semigroup_left_sum_not_trivial S T aS aT). 
   reflexivity. 
Defined. 


Lemma checked_annotated_right_sum: 
    ∀ S T : Type,  ∀ aS : AnnotatedSemigroup S, ∀ aT : AnnotatedSemigroup T, 
      checked_semigroup_right_sum S T 
           (annotated_semigroup_to_checked_semigroup S aS)
           (annotated_semigroup_to_checked_semigroup T aT)
      = annotated_semigroup_to_checked_semigroup _ 
          (annotated_semigroup_right_sum S T aS aT). 
Proof. 
   intros S T aS aT. 
   (* unwind RHS *) 
   unfold annotated_semigroup_to_checked_semigroup at 3. 
   unfold semigroup_proofs_to_checks. 
(*    rewrite (rewrite_test S T aS aT). *) 

   (* unwind LHS *) 
   unfold annotated_semigroup_to_checked_semigroup. 
   unfold checked_semigroup_right_sum. 
   unfold fst, snd. 

   (* rewrite LHS to become RHS *) 
   rewrite (annotated_semigroup_right_sum_projT1 S T aS aT) at 1. 
   rewrite (correct_checked_semigroup_right_sum_commutative S T aS aT). 
   rewrite (correct_checked_semigroup_right_sum_selective S T aS aT). 
   rewrite (correct_checked_semigroup_right_sum_is_left S T aS aT). 
   rewrite (correct_checked_semigroup_right_sum_is_right S T aS aT). 
   rewrite (correct_checked_semigroup_right_sum_idempotent S T aS aT). 
   rewrite (correct_checked_semigroup_right_sum_not_trivial S T aS aT). 
   reflexivity. 
Defined. 


Lemma checked_annotated_left : 
    ∀ S : Type,  ∀ aS : AnnotatedEQV S, 
      checked_semigroup_left S (annotated_eqv_to_checked_eqv S aS)
      = annotated_semigroup_to_checked_semigroup S (annotated_semigroup_left S aS). 
Proof. 
   intros S aS. 
   (* unwind RHS *) 
   unfold annotated_semigroup_to_checked_semigroup. 
   unfold semigroup_proofs_to_checks. 

   (* unwind LHS *) 
   unfold annotated_eqv_to_checked_eqv. 
   unfold checked_semigroup_left. 
   unfold fst, snd. 

   (* make LHS = RHS *) 
   destruct aS.  destruct e. destruct eqv_not_trivial0 as [s1 [s2 pS]]; simpl. 
   reflexivity. 
Defined. 


Lemma checked_annotated_right : 
    ∀ S : Type,  ∀ aS : AnnotatedEQV S, 
      checked_semigroup_right S (annotated_eqv_to_checked_eqv S aS)
      = annotated_semigroup_to_checked_semigroup S (annotated_semigroup_right S aS). 
Proof. 
   intros S aS. 
   (* unwind RHS *) 
   unfold annotated_semigroup_to_checked_semigroup. 
   unfold semigroup_proofs_to_checks. 

   (* unwind LHS *) 
   unfold annotated_eqv_to_checked_eqv. 
   unfold checked_semigroup_right. 
   unfold fst, snd. 

   (* make LHS = RHS *) 
   destruct aS.  destruct e. destruct eqv_not_trivial0 as [s1 [s2 pS]]; simpl.
   reflexivity. 
Defined. 

Lemma checked_annotated_concat : 
    ∀ S : Type,  ∀ aS : AnnotatedEQV S, 
      checked_semigroup_concat S (annotated_eqv_to_checked_eqv S aS)
      = annotated_semigroup_to_checked_semigroup (list S) (annotated_semigroup_concat S aS). 
Proof. 
   intros S aS. 
   (* unwind RHS *) 
   unfold annotated_semigroup_to_checked_semigroup. 
   unfold semigroup_proofs_to_checks. 

   (* unwind LHS *) 
   unfold annotated_eqv_to_checked_eqv. 
   unfold checked_semigroup_concat. 
   unfold fst, snd. 

   (* make LHS = RHS *) 
   destruct aS.  destruct e. destruct eqv_not_trivial0 as [s1 [s2 pS]]; simpl.
   reflexivity. 
Defined. 

Lemma checked_annotated_union : 
    ∀ S : Type,  ∀ aS : AnnotatedEQV S, 
      checked_semigroup_union S (annotated_eqv_to_checked_eqv S aS)
      = annotated_semigroup_to_checked_semigroup (finite_set S) (annotated_semigroup_union S aS). 
Proof. 
   intros S aS. 
   (* unwind RHS *) 
   unfold annotated_semigroup_to_checked_semigroup. 
   unfold semigroup_proofs_to_checks. 

   (* unwind LHS *) 
   unfold annotated_eqv_to_checked_eqv. 
   unfold checked_semigroup_union. 
   unfold fst, snd. 

   (* make LHS = RHS *) 
   destruct aS.  destruct e. destruct eqv_not_trivial0 as [s1 [s2 pS]]; simpl.
   reflexivity. 
Defined. 



Theorem sg_checked_sem_correct : 
        ∀ t : te,  ∀ e : tSG t,
           sg_checked_sem t e 
         = annotated_semigroup_to_checked_semigroup (te_to_Type t) (sg_annotated_sem t e). 
Proof. 
       intro t. induction e; unfold annotated_semigroup_to_checked_semigroup. 
       simpl. reflexivity. 
       simpl. reflexivity. 
       simpl. induction n. reflexivity. 
       simpl. induction n. reflexivity. 
       simpl. induction n. reflexivity. 
       simpl. induction n. reflexivity. 
       simpl. rewrite IHe1, IHe2. rewrite checked_annotated_left_sum. simpl.  reflexivity. 
       simpl. rewrite IHe1, IHe2. rewrite checked_annotated_right_sum. simpl.  reflexivity. 
       simpl. rewrite IHe1, IHe2. rewrite checked_annotated_product. simpl.  reflexivity. 
       unfold sg_checked_sem . unfold sg_annotated_sem. rewrite eqv_checked_sem_correct. 
          rewrite checked_annotated_left. simpl.  reflexivity. 
       unfold sg_checked_sem . unfold sg_annotated_sem. rewrite eqv_checked_sem_correct. 
          rewrite checked_annotated_right. simpl.  reflexivity. 
       unfold sg_checked_sem . unfold sg_annotated_sem. rewrite eqv_checked_sem_correct. 
          rewrite checked_annotated_concat. simpl.  reflexivity. 
       unfold sg_checked_sem . unfold sg_annotated_sem. rewrite eqv_checked_sem_correct. 
          rewrite checked_annotated_union. simpl.  reflexivity. 
Defined. 

Definition sgr_checked : ∀ s : SG,
       DD {x : te & tSG x} 
          Error 
          (λ p : {x : te & tSG x}, CheckedSemigroup (te_to_Type (projT1 p)))
          (sg_infer s)
:= λ s,  option_app2 _ _ _ _ (sg_infer s) sg_checked_sem. 

Definition sgr_annotated : ∀ s : SG,
       DD {x : te & tSG x} 
          Error 
          (λ p : {x : te & tSG x}, AnnotatedSemigroup (te_to_Type (projT1 p)))
          (sg_infer s)
:= λ s,  option_app2 _ _ _ _ (sg_infer s) sg_annotated_sem. 


