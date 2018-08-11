Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts. 

Section Theory.

Open Scope list_scope. 

Lemma brel_list_symmetric : ∀ (S : Type) (r : brel S), 
              (brel_symmetric _ r) → brel_symmetric (list S) (brel_list r). 
Proof. unfold brel_symmetric. 
       induction s; induction t; simpl; intros; auto.        
          apply andb_is_true_right. 
          apply andb_is_true_left in H0. 
          destruct H0 as [H0_l H0_r]. 
          split. 
             apply (H _ _ H0_l). 
             apply (IHs t H0_r).
Qed. 

Lemma brel_list_reflexive : ∀ (S : Type) (r : brel S), 
              (brel_reflexive _ r) → brel_reflexive (list S) (brel_list r). 
Proof. unfold brel_reflexive. induction s; simpl; auto.  
       rewrite (H a). rewrite IHs. simpl. reflexivity. 
Qed.

Lemma brel_list_transitive : ∀ (S : Type) (r : brel S), 
              (brel_transitive _ r) → brel_transitive (list S) (brel_list r). 
Proof. unfold brel_transitive. 
       induction s; induction t; induction u; simpl; intros; auto.        
          discriminate. 
          apply andb_is_true_right. 
          apply andb_is_true_left in H0. 
          apply andb_is_true_left in H1. 
          destruct H0 as [H0_l H0_r]. 
          destruct H1 as [H1_l H1_r]. 
          split. 
             apply (H _ _ _ H0_l H1_l). 
             apply (IHs t u H0_r H1_r).
Qed. 


Lemma brel_list_congruence : ∀ (S : Type) (r : brel S), 
         brel_symmetric S r -> 
         brel_transitive S r -> 
         brel_congruence S r r -> 
              brel_congruence (list S) (brel_list r) (brel_list r). 
Proof. intros S r symS transS congS s t u v.  
       apply brel_congruence_self. 
       apply brel_list_symmetric; auto. 
       apply brel_list_transitive; auto. 
Qed. 

Open Scope nat.

Lemma cons_length : ∀ (T : Type) (t : T ) (l : list T), length (t :: l) = S(length l). 
Proof. intros T t l. simpl. reflexivity. Qed.

Lemma brel_list_true_implies_length_equal :
  ∀ (S : Type) (r : brel S) (l1 l2 : list S),
    brel_list  r l1 l2 = true -> (length l1) = (length l2).
Proof. intros S r. induction l1; induction l2; intro H. 
       reflexivity. 
       compute in H. discriminate.
       compute in H. discriminate.        
       unfold brel_list in H. fold (@brel_list S) in H.
       apply andb_is_true_left in H.
       destruct H as [_ H].
       rewrite cons_length. rewrite cons_length.
       apply IHl1 in H. auto.        
Qed. 

Lemma list_length_not_equal_implies_brel_list_false :
       ∀ (S : Type) (r : brel S) (l1 l2 : list S), 
           (length l1) <> (length l2) -> 
               brel_list r l1 l2 = false. 
Proof. intros S r l1 l2 H. 
       case_eq (brel_list r l1 l2); intro F.
       apply brel_list_true_implies_length_equal in F. elim H. assumption.
       reflexivity. 
Qed. 

Lemma brel_list_not_cons_equal_left : ∀ (S : Type) (r : brel S) (l : list S) (s : S), 
                                     brel_list r (s :: l) l = false. 
Proof. intros S r l s. apply list_length_not_equal_implies_brel_list_false. 
       rewrite cons_length. assert (fact := n_Sn (length l)). 
       intro F. rewrite F in fact. elim fact. reflexivity. 
Qed.

Lemma brel_list_not_cons_equal_right : ∀ (S : Type) (r : brel S) (l : list S) (s : S), 
        brel_list r l (s :: l) = false. 
Proof. intros S r l s. apply list_length_not_equal_implies_brel_list_false. 
       rewrite cons_length. assert (fact := n_Sn (length l)). 
       intro F. rewrite <- F in fact. elim fact. reflexivity. 
Qed.


Lemma list_length_zero : ∀ (S : Type) (u : list S), length u = 0 -> u = nil.
Proof. intro S. induction u; auto. intro H.
       rewrite cons_length in H.
       assert (fact1 := PeanoNat.Nat.neq_succ_0 (length u)).  
       rewrite H in fact1.
       discriminate.
Qed. 


Lemma plus_zero_only_left_id : ∀ a b : nat, b = a + b -> a = 0. 
Proof. induction a; auto. 
       induction b; intro H.
       assert (fact1 := PeanoNat.Nat.add_0_r (S a)).
       rewrite fact1 in H. rewrite H. reflexivity.
       rewrite plus_SS in H. 
       apply eq_add_S in H.
       rewrite <- plus_Sn_m in H.
       apply IHb; auto. 
Qed. 

Lemma concat_nil_only_left_id : ∀ (S : Type) (r : brel S) (a : S) (w u : list S),  
    brel_list r w (u ++ w) = true -> brel_list r nil u = true. 
Proof. intros S r a w u H. 
       apply brel_list_true_implies_length_equal in H.
       rewrite List.app_length in H. 
       assert (fact1 := plus_zero_only_left_id (length u) (length w) H). 
       rewrite (list_length_zero _ u fact1).
       compute. reflexivity.
Qed. 

Lemma concat_cons_no_left_id : ∀ (S : Type) (a : S) (r : brel S) (s u : list S),  
    brel_list r s (u ++ a :: s) = false .
Proof. intros S r a s u.
       case_eq (brel_list a s (u ++ r :: s)); intro H.
       assert (K := H). 
       apply brel_list_true_implies_length_equal in H.
       rewrite List.app_length in H.
       rewrite cons_length in H.
       (* Oh no!  Arithmetic in Coq! *) 
       rewrite PeanoNat.Nat.add_comm in H. 
       apply Minus.plus_minus in H.
       rewrite PeanoNat.Nat.sub_succ_r in H. 
       rewrite <- Minus.minus_diag_reverse in H. 
       rewrite PeanoNat.Nat.pred_0 in H. 
       apply list_length_zero in H.  rewrite H in K. simpl in K.
       rewrite brel_list_not_cons_equal_right in K. rewrite K.
       reflexivity.        
       reflexivity. 
Qed. 

Lemma concat_cons_no_left_id_v2 : ∀ (S : Type) (a : S) (r : brel S) (s u : list S),  
       brel_list r (u ++ a :: s) s = false .   
Proof. intros S r a s u.
       case_eq (brel_list a (u ++ r :: s) s); intro H.
       assert (K := H). 
       apply brel_list_true_implies_length_equal in H.
       rewrite List.app_length in H.
       rewrite cons_length in H.
       (* Oh no!  Arithmetic in Coq! *)
       apply eq_sym in H.
       rewrite PeanoNat.Nat.add_comm in H. 
       apply  Minus.plus_minus in H.
       rewrite PeanoNat.Nat.sub_succ_r in H. 
       rewrite <- Minus.minus_diag_reverse in H. 
       rewrite PeanoNat.Nat.pred_0 in H. 
       apply list_length_zero in H.  rewrite H in K. rewrite List.app_nil_l in K. 
       rewrite brel_list_not_cons_equal_left in K. rewrite K.
       reflexivity.        
       reflexivity. 
Qed. 

(*


Lemma brel_list_rep_correct : ∀ (S : Type)(eq : brel S)(rep : unary_op S), 
          brel_rep_correct S eq rep →
              brel_rep_correct (list S) (brel_list eq) (uop_list_map rep). 
Proof. intros S eq rep P l. induction l. 
       simpl. reflexivity. 
       simpl. apply andb_is_true_right. split. 
          apply P. 
          assumption. 
Defined. 


Lemma brel_list_rep_idempotent : ∀ (S : Type)(eq : brel S)(rep : unary_op S), 
          brel_rep_idempotent S eq rep →
              brel_rep_idempotent (list S) (brel_list eq) (uop_list_map rep). 
Proof. intros S eq rep P l. induction l. 
       simpl. reflexivity. 
       simpl. apply andb_is_true_right. split. 
          apply P. 
          assumption. 
Defined. 

 *)


Lemma brel_list_not_trivial : ∀ (S : Type) (r : brel S) (s : S) (f : S -> S), 
              (brel_symmetric S r) → 
              (brel_not_trivial S r f) → brel_not_trivial (list S) (brel_list r) (λ (l : list S), s :: l). 
Proof. intros S r s f symS Pf l.  
       assert (F1 : brel_list r (s :: l) l = false). 
         apply brel_list_not_cons_equal_left. 
       assert (F2 : brel_list r l (s :: l) = false). 
         apply brel_symmetric_implies_dual. 
         apply brel_list_symmetric. assumption. 
         assumption. 
       rewrite F1, F2; auto. 
Defined. 


(* a few useful lemmas *) 

Lemma list_concat_cons : ∀ (S : Type) (r : brel S),
    brel_reflexive S r ->
    ∀ (a : S) (t s : list S),
        brel_list r (t ++ (a :: s)) ((t ++ (a :: nil)) ++ s) = true.
Proof. intros S r ref a.  induction t; intros s; simpl. 
       apply andb_is_true_right. split.  
          apply ref.
          apply brel_list_reflexive; auto. 
       apply andb_is_true_right. split.
          apply ref.
          apply IHt. 
Qed. 


End Theory.


Section ACAS.
Open Scope list_scope. 

Definition eqv_proofs_brel_list : ∀ (S : Type) (r : brel S), eqv_proofs S r → eqv_proofs (list S) (brel_list r) 
:= λ S r eqv, 
   {| 
     A_eqv_congruence  := brel_list_congruence S r 
                                  (A_eqv_symmetric S r eqv) 
                                  (A_eqv_transitive S r eqv) 
                                  (A_eqv_congruence S r eqv) 
   ; A_eqv_reflexive   := brel_list_reflexive S r  (A_eqv_reflexive S r eqv) 
   ; A_eqv_transitive  := brel_list_transitive S r (A_eqv_transitive S r eqv) 
   ; A_eqv_symmetric   := brel_list_symmetric S r  (A_eqv_symmetric S r eqv) 
   |}. 


Definition A_eqv_list : ∀ (S : Type),  A_eqv S -> A_eqv (list S) 
:= λ S eqvS, 
   {| 
      A_eqv_eq     := brel_list (A_eqv_eq S eqvS)
    ; A_eqv_proofs := eqv_proofs_brel_list S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS)                                                                   

    ; A_eqv_witness := nil 
    ; A_eqv_new     := λ (l : list S), (A_eqv_witness S eqvS) :: l
    ; A_eqv_not_trivial := brel_list_not_trivial S
                             (A_eqv_eq S eqvS)
                             (A_eqv_witness S eqvS)
                             (A_eqv_new S eqvS)
                             (A_eqv_symmetric S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS))
                             (A_eqv_not_trivial S eqvS)

    ; A_eqv_data   := λ l, DATA_list (List.map (A_eqv_data S eqvS) l)
    ; A_eqv_rep    := λ l, List.map (A_eqv_rep S eqvS) l
    ; A_eqv_ast    := Ast_eqv_list (A_eqv_ast S eqvS)
   |}. 

End ACAS.

Section CAS.

Definition eqv_list : ∀ {S : Type},  eqv (S := S) -> @eqv (list S)
:= λ {S} eqvS, 
   {| 
      eqv_eq    := brel_list (eqv_eq eqvS) 
    ; eqv_witness := nil 
    ; eqv_new := (λ (l : list S), (eqv_witness eqvS) :: l)
    ; eqv_data  := λ l, DATA_list (List.map (eqv_data eqvS) l)
    ; eqv_rep   := λ l, List.map (eqv_rep eqvS) l
    ; eqv_ast   := Ast_eqv_list (eqv_ast eqvS)
   |}. 

End CAS.

Section Verify.

Theorem correct_eqv_list : ∀ (S : Type) (E : A_eqv S),  
         eqv_list (A2C_eqv S E) = A2C_eqv (list S) (A_eqv_list S E). 
Proof. intros S E. destruct E. compute . reflexivity. Qed. 
  
 
End Verify.   
  