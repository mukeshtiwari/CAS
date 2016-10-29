Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.facts. 

Open Scope list_scope. 



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



Lemma cons_length : ∀ (T : Type) (t : T ) (l : list T), length (t :: l) = S(length l). 
Proof. intros T t l. unfold length. reflexivity. Qed. 

Lemma list_length_not_equal_implies_brel_list_false :
       ∀ (S : Type) (r : brel S) (l1 l2 : list S), 
           (length l1) <> (length l2) -> 
               brel_list S r l1 l2 = false. 
Proof. intros S r. induction l1; induction l2; intro H. 
       compute in H. elim H. reflexivity. 
       unfold brel_list. reflexivity. 
       unfold brel_list. reflexivity. 
       unfold brel_list. fold brel_list. 
       rewrite andb_comm.  rewrite IHl1. simpl. reflexivity. 
          intro F. elim H. rewrite cons_length. rewrite cons_length. 
          rewrite F. reflexivity. 
Qed. 


Lemma bop_concat_cons_not_equal : ∀ (S : Type) (r : brel S) (l : list S) (s : S), 
                                     brel_list S r (s :: l) l = false. 
Proof. intros S r l s. apply list_length_not_equal_implies_brel_list_false. 
       rewrite cons_length. assert (fact := n_Sn (length l)). 
       intro F. rewrite F in fact. elim fact. reflexivity. 
Qed. 



Lemma brel_list_witness : ∀ (S : Type) (r : brel S), brel_witness (list S) (brel_list S r). 
Proof. intros S r. exists nil; auto. Defined.

Lemma brel_list_negate : ∀ (S : Type) (r : brel S), 
              (brel_symmetric _ r) → 
              (brel_nontrivial S r) → brel_negate (list S) (brel_list S r). 
Proof. unfold brel_negate. 
       intros S r symS ntS.  
       destruct (brel_nontrivial_witness S r ntS) as [s Ps]. 
       destruct (brel_nontrivial_negate S r ntS) as [f Pf]. 
       exists (λ (l : list S), s :: l). intro l.
       assert (F1 : brel_list S r (s :: l) l = false). 
         apply bop_concat_cons_not_equal. 
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









