
Definition brel2_lift_list_left : ∀ S : Type, brel S → brel2 (list S) S
:= λ S r X a, bProp_lift_list S (bProp_from_brel_left S r a) X. 

Definition brel2_lift_list_right : ∀ S : Type, brel S → brel2 S (list S)
:= λ S r a, bProp_lift_list S (bProp_from_brel_right S r a). 


Definition brel2_lift_set_left : ∀ S : Type, brel S → brel2 (finite_set S) S
:= brel2_lift_list_left.

Definition brel2_lift_set_right : ∀ S : Type, brel S → brel2 S (finite_set S)
:= brel2_lift_list_right. 


Definition is_minimal_in : ∀ S : Type, brel S → brel S → brel2 (finite_set S) S 
:= λ S eq lte, brel2_lift_set_left S (brel_dual S (brel_strictify S lte)).                  

Lemma brel2_conjunction_congruence : 
  ∀ (S T : Type) (rS : brel S) (rT : brel T) (r1 : brel2 S T) (r2 : brel2 S T) , 
   brel2_congruence S T rS rT r1 -> 
   brel2_congruence S T rS rT r2 -> 
    brel2_congruence S T rS rT (brel2_conjunction S T r1 r2).  
Proof. unfold brel2_congruence.  
       intros S T rS rT r1 r2 C1 C2 s1 s2 t1 t2 H1 H2. 
       unfold brel2_conjunction. 
       assert (Q1 := C1 _ _ _ _ H1 H2). 
       assert (Q2 := C2 _ _ _ _ H1 H2). 
       rewrite Q1, Q2. 
       reflexivity. 
Qed. 


Lemma brel2_reverse_congruence : 
  ∀ (S T : Type) (rS : brel S) (rT : brel T) (r : brel2 S T), 
   brel2_congruence S T rS rT r -> 
    brel2_congruence T S rT rS (brel2_reverse S T r ).  
Proof. unfold brel2_congruence.  
       intros S T rS rT r C s1 s2 t1 t2 H1 H2. 
       assert (Q := C _ _ _ _ H2 H1). 
       unfold brel2_reverse. 
       assumption. 
Qed. 



Hypothesis brel2_in_set_congruence : 
  ∀ (S : Type) (rS : brel S), 
    brel2_congruence (finite_set S) S (brel_set S rS) rS (in_set S rS). 

Hypothesis brel2_lift_set_right_congruence : 
  ∀ (S : Type) (eqS rS : brel S), 
   brel2_congruence S (finite_set S) eqS (brel_set S eqS) (brel2_lift_set_right S rS).  


Lemma brel2_is_minimal_in_congruence: 
  ∀ (S : Type) (eq lte : brel S), 
    brel2_congruence S (finite_set S) eq (brel_set S eq) (is_minimal_in S eq lte). 
Proof. intros S eq lte. 
       unfold is_minimal_in.        
       apply brel2_conjunction_congruence. 
       apply brel2_reverse_congruence.
       apply brel2_in_set_congruence. 
       apply brel2_lift_set_right_congruence. 
Qed. 

Lemma is_minimal_in_true_not_nil : 
    ∀ (S : Type) (eq : brel S) (lt : brel S) (a : S) (s : finite_set S),
          is_minimal_in S eq lt a s = true -> s ≠ nil. 
Proof. intros S eq lt a s H. destruct s. compute in H. discriminate. apply cons_not_nil. Defined. 


Definition bop_reduce : ∀ (S : Type),  unary_op S -> binary_op S -> binary_op S 
:= λ S u b x y,  u (b x y). 

Lemma bop_reduce_idempotent : ∀ (S : Type) (rS : brel S) (uS : unary_op S) (bS : binary_op S), 
         brel_symmetric S rS -> 
         brel_transitive S rS -> 
         uop_congruence S rS uS -> 
         uop_idempotent S rS uS -> 
         bop_idempotent S rS bS -> 
         uop_bop_reduction S rS uS bS -> 
         bop_idempotent S (brel_reduce S rS uS) (bop_reduce S uS bS). 
Proof. intros S rS uS bS symS transS cong_uS idem_uS idem_bS red a. 
       unfold brel_reduce, bop_reduce. 

       assert (A : rS (uS (uS (bS (uS a) (uS a)))) (uS (bS (uS a) (uS a))) = true). 
          apply idem_uS. 
       assert (B : rS (uS (bS a a)) (uS (bS (uS a) (uS a)))  = true).
          apply red. apply symS in B. 
       assert (C : rS (uS (bS a a)) (uS a) = true). 
          assert (H := idem_bS a). 
          apply cong_uS. assumption. 
      assert (D := transS _ _ _ B C). 
      assert (E := transS _ _ _ A D). 
      assumption. 
Qed. 


Lemma bop_reduce_not_idempotent_1 : ∀ (S : Type) (rS : brel S) (uS : unary_op S) (bS : binary_op S), 
         brel_symmetric S rS -> 
         brel_transitive S rS -> 
         uop_congruence S rS uS -> 
         uop_idempotent S rS uS -> 
         bop_not_idempotent S rS bS -> (****) 
         uop_bop_reduction S rS uS bS -> 
         (∀ s t : S, rS s t = false -> rS (uS s) (uS t) = false)  -> (***) 
         bop_not_idempotent S (brel_reduce S rS uS) (bop_reduce S uS bS). 
Proof. intros S rS uS bS symS transS cong_uS idem_uS [a Fb] red C. 
       unfold bop_not_idempotent, brel_reduce, bop_reduce. 
       exists a. 
       assert (A : rS (uS (uS (bS (uS a) (uS a)))) (uS (bS a a)) = true). admit.   
       assert (B : rS (uS (bS a a)) (uS a) = false). apply C. assumption. 
       case_eq(rS (uS (uS (bS (uS a) (uS a)))) (uS a)); intro D; auto. 
          apply symS in A. 
          assert (E := transS _ _ _ A D). rewrite E in B.  assumption.
Qed. 


Lemma tmp : ∀ (S : Type) (rS : brel S) (uS : unary_op S), 
            (∀ s t : S, rS (uS s) (uS t) = true -> rS s t = true)
            -> 
            (∀ s t : S, (rS s t = false) -> (rS (uS s) (uS t) = false)). 
Proof. intros. 
       case_eq(rS (uS s) (uS t)); intro F; auto. 
       rewrite (H s t F) in H0. assumption. 
Qed. 


Lemma bop_reduce3_idempotent : ∀ (S : Type) (rS : brel S) (uS : unary_op S) (bS : binary_op S), 
         uop_congruence S rS uS -> 
         bop_idempotent S rS bS -> 
         bop_idempotent S (brel_reduce S rS uS) bS. 
Proof. intros S rS uS bS cong_uS idem_bS a. 
       unfold brel_reduce, bop_reduce. 
       assert (H := idem_bS a). 
       apply cong_uS. assumption. 
Qed. 


Lemma bop_reduce3_not_idempotent_1 : ∀ (S : Type) (rS : brel S) (uS : unary_op S) (bS : binary_op S), 
         uop_congruence S rS uS -> 
         bop_not_idempotent S rS bS -> 
         (∀ s t : S, (rS s t = false) -> (rS (uS s) (uS t) = false)) -> (**uop_cancellative*) 
         bop_not_idempotent S (brel_reduce S rS uS) bS. 
Proof. intros S rS uS bS cong_uS [a Pa] C. 
       unfold brel_reduce, bop_reduce. 
       exists a. apply C. assumption. 
Qed. 

Variable left_monotone : ∀ a b c : S, a <== b -> c[*]a <== c[*]b. 

Lemma left_strict_monotone : ∀ a b c : S, a << b -> c[*]a << c[*]b. 
Proof. intros a b c. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; 
       case_eq(lte (c[*]a) (c[*]b)); intro H3; 
       case_eq(lte (c[*]b) (c[*]a)); intro H4; auto; intro T. 
          assert (F1 := antisym_lte _ _ H3 H4). 
          (* show a < b and c[*]a == c[*]b -> false *) 
          admit. 
          (* show a < b and c[*]b < c[*]a -> false *) 
          admit. 
          (* show a < b and c[*]b # c[*]a -> false *)           
          admit. 
Qed. 

(* 
Open Scope nat. 
Compute (7 + 7). 
Compute (brel_dual nat (brel_strictify nat brel_le_nat) 4 5). 



Lemma brel2_is_minimal_in_true_elim : ∀ (S : Type) (eq lte : brel S) (X : finite_set S) (a : S), 
       (is_minimal_in S eq lte a X = true) -> 
           (in_set S eq X a = true) *  
           ∀ (x : S), in_set S eq X x = true ->  (brel_dual S (brel_strictify S lte) x a = true). 
Proof. intros S eq lte X. induction X. 
       intros. compute in H. discriminate. 
       intros b H. 
       unfold is_minimal_in in H. 
       unfold brel2_conjunction in H. 
       apply andb_is_true_left in H. destruct H as [L R].
       unfold brel2_reverse in L. split. 
          assumption. 
      unfold brel2_lift_set_right in R. 
      unfold brel2_lift_list_right  in R.
      intros x J. 
      unfold bProp_lift_list in R. 
compute. 
       case_eq(lte x a); intro Q1; case_eq(lte a x); intro Q2; simpl; auto. 
Qed. 
*) 
