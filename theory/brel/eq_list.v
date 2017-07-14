Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.facts. 

Open Scope list_scope. 


Lemma brel_list_witness : ∀ (S : Type) (r : brel S), brel_witness (list S) (brel_list S r). 
Proof. intros S r. exists nil; auto. Defined.

Lemma brel_list_symmetric : ∀ (S : Type) (r : brel S), 
              (brel_symmetric _ r) → brel_symmetric (list S) (brel_list S r). 
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
              (brel_reflexive _ r) → brel_reflexive (list S) (brel_list S r). 
Proof. unfold brel_reflexive. induction s; simpl; auto.  
       rewrite (H a). rewrite IHs. simpl. reflexivity. 
Qed.

Lemma brel_list_transitive : ∀ (S : Type) (r : brel S), 
              (brel_transitive _ r) → brel_transitive (list S) (brel_list S r). 
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
              brel_congruence (list S) (brel_list S r) (brel_list S r). 
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
    brel_list S r l1 l2 = true -> (length l1) = (length l2).
Proof. intros S r. induction l1; induction l2; intro H. 
       reflexivity. 
       compute in H. discriminate.
       compute in H. discriminate.        
       unfold brel_list in H. fold brel_list in H.
       apply andb_is_true_left in H.
       destruct H as [_ H].
       rewrite cons_length. rewrite cons_length.
       apply IHl1 in H. auto.        
Qed. 

Lemma list_length_not_equal_implies_brel_list_false :
       ∀ (S : Type) (r : brel S) (l1 l2 : list S), 
           (length l1) <> (length l2) -> 
               brel_list S r l1 l2 = false. 
Proof. intros S r l1 l2 H. 
       case_eq (brel_list S r l1 l2); intro F.
       apply brel_list_true_implies_length_equal in F. elim H. assumption.
       reflexivity. 
Qed. 

Lemma brel_list_not_cons_equal_left : ∀ (S : Type) (r : brel S) (l : list S) (s : S), 
                                     brel_list S r (s :: l) l = false. 
Proof. intros S r l s. apply list_length_not_equal_implies_brel_list_false. 
       rewrite cons_length. assert (fact := n_Sn (length l)). 
       intro F. rewrite F in fact. elim fact. reflexivity. 
Qed.

Lemma brel_list_not_cons_equal_right : ∀ (S : Type) (r : brel S) (l : list S) (s : S), 
        brel_list S r l (s :: l) = false. 
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
    brel_list S r w (u ++ w) = true -> brel_list S r nil u = true. 
Proof. intros S r a w u H. 
       apply brel_list_true_implies_length_equal in H.
       rewrite List.app_length in H. 
       assert (fact1 := plus_zero_only_left_id (length u) (length w) H). 
       rewrite (list_length_zero _ u fact1).
       compute. reflexivity.
Qed. 

Lemma concat_cons_no_left_id : ∀ (S : Type) (a : S) (r : brel S) (s u : list S),  
    brel_list S r s (u ++ a :: s) = false .
Proof. intros S r a s u.
       case_eq (brel_list S a s (u ++ r :: s)); intro H.
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
       brel_list S r (u ++ a :: s) s = false .   
Proof. intros S r a s u.
       case_eq (brel_list S a (u ++ r :: s) s); intro H.
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


Lemma brel_list_negate : ∀ (S : Type) (r : brel S), 
              (brel_symmetric _ r) → 
              (brel_nontrivial S r) → brel_negate (list S) (brel_list S r). 
Proof. unfold brel_negate. 
       intros S r symS ntS.  
       destruct (brel_nontrivial_witness S r ntS) as [s Ps]. 
       destruct (brel_nontrivial_negate S r ntS) as [f Pf]. 
       exists (λ (l : list S), s :: l). intro l.
       assert (F1 : brel_list S r (s :: l) l = false). 
         apply brel_list_not_cons_equal_left. 
       assert (F2 : brel_list S r l (s :: l) = false). 
         apply brel_symmetric_implies_dual. 
         apply brel_list_symmetric. assumption. 
         assumption. 
       rewrite F1, F2; auto. 
Defined. 

Definition brel_list_nontrivial : ∀ (S : Type) (r : brel S), 
       (brel_symmetric _ r) → 
       (brel_nontrivial S r) → brel_nontrivial (list S) (brel_list S r)
:= λ S r symS nt, 
   {| 
      brel_nontrivial_witness := brel_list_witness S r
    ; brel_nontrivial_negate  := brel_list_negate S r symS nt
   |}. 


Lemma brel_list_rep_correct : ∀ (S : Type)(eq : brel S)(rep : unary_op S), 
          brel_rep_correct S eq rep →
              brel_rep_correct (list S) (brel_list S eq) (uop_list_map S rep). 
Proof. intros S eq rep P l. induction l. 
       simpl. reflexivity. 
       simpl. apply andb_is_true_right. split. 
          apply P. 
          assumption. 
Defined. 


Lemma brel_list_rep_idempotent : ∀ (S : Type)(eq : brel S)(rep : unary_op S), 
          brel_rep_idempotent S eq rep →
              brel_rep_idempotent (list S) (brel_list S eq) (uop_list_map S rep). 
Proof. intros S eq rep P l. induction l. 
       simpl. reflexivity. 
       simpl. apply andb_is_true_right. split. 
          apply P. 
          assumption. 
Defined. 



(* a few useful lemmas *) 

Lemma list_concat_cons : ∀ (S : Type) (r : brel S),
    brel_reflexive S r ->
    ∀ (a : S) (t s : list S),
        brel_list S r (t ++ (a :: s)) ((t ++ (a :: nil)) ++ s) = true.
Proof. intros S r ref a.  induction t; intros s; simpl. 
       apply andb_is_true_right. split.  
          apply ref.
          apply brel_list_reflexive; auto. 
       apply andb_is_true_right. split.
          apply ref.
          apply IHt. 
Qed. 

Close Scope nat.








