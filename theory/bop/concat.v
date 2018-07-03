Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.eq_list. 

Open Scope list_scope.

Lemma bop_concat_not_idempotent : 
     ∀ (S : Type) (r : brel S) (s : S), 
           bop_not_idempotent (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s. unfold bop_not_idempotent. exists (s :: nil). simpl. 
       rewrite andb_comm. simpl. reflexivity. 
Defined. 

Lemma bop_concat_not_commutative : 
   ∀ (S : Type) (r : brel S) (s : S) (f : S -> S), (brel_not_trivial S r f) -> bop_not_commutative (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s f fP. 
       exists (s :: nil, (f s) :: nil). unfold bop_concat. 
       rewrite <- List.app_comm_cons. rewrite <- List.app_comm_cons. 
       rewrite List.app_nil_l. rewrite List.app_nil_l.
       unfold brel_list. destruct (fP s) as [L R]. rewrite L. simpl.  reflexivity. 
Defined. 

Lemma bop_concat_not_selective : 
   ∀ (S : Type) (r : brel S) (s : S) (f : S -> S), brel_not_trivial S r f -> bop_not_selective (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s f fP. 
       exists (s :: nil, (f s) :: nil). 
       rewrite <- List.app_comm_cons. rewrite List.app_nil_l. 
       unfold brel_list.  destruct (fP s) as [L R]. 
       rewrite L, andb_comm.  simpl. auto. 
Defined. 


Lemma bop_concat_congruence : 
   ∀ (S : Type) (r : brel S),  (brel_reflexive S r) -> bop_congruence (list S) (@brel_list S r) (@bop_concat S).
Proof. unfold bop_congruence, bop_concat. intros S r refS. 
       induction s1; induction s2; induction t1; induction t2; unfold brel_list; intros H Q. 
       rewrite List.app_nil_l. reflexivity. 
       discriminate. discriminate. discriminate. discriminate. 
       fold @brel_list. rewrite List.app_nil_l. rewrite List.app_nil_l. 
          fold @brel_list in Q. unfold brel_list. fold @brel_list. assumption.
       discriminate. discriminate. discriminate. discriminate. 
       fold @brel_list. rewrite List.app_nil_r. rewrite List.app_nil_r. 
          fold @brel_list in H. unfold brel_list. fold @brel_list. assumption.
       discriminate. discriminate. discriminate. discriminate. 
       fold @brel_list. fold @brel_list in H, Q. 
       rewrite <- List.app_comm_cons. rewrite <- List.app_comm_cons.
       unfold brel_list. fold @brel_list. 
       destruct (andb_is_true_left _ _ H) as [H1 H2]. 
       rewrite H1. simpl. 
       apply IHs1. assumption. 
       unfold brel_list. fold @brel_list. assumption. 
Qed. 


Lemma bop_concat_associative : 
   ∀ (S : Type) (r : brel S),  (brel_reflexive S r) -> bop_associative (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r refS. unfold bop_concat, bop_associative. 
       intros s t u. 
       rewrite List.app_assoc. 
       apply brel_list_reflexive. assumption. 
Qed. 

Lemma bop_concat_not_is_left : 
   ∀ (S : Type) (r : brel S) (s : S), bop_not_is_left (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s. unfold bop_concat, bop_not_is_left. 
       exists (nil, s :: nil). rewrite List.app_nil_l. 
       unfold brel_list. reflexivity. 
Defined. 


Lemma bop_concat_not_is_right : 
   ∀ (S : Type) (r : brel S) (s : S), bop_not_is_right (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s. unfold bop_concat, bop_not_is_right. 
       exists (s :: nil, nil). rewrite List.app_nil_r. 
       unfold brel_list. reflexivity. 
Defined. 

Lemma bop_concat_exists_id : ∀ (S : Type) (r : brel S), 
                  brel_reflexive S r -> bop_exists_id (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r refS. exists nil. intro s. split. 
          unfold bop_concat. rewrite List.app_nil_l. apply brel_list_reflexive; auto. 
          unfold bop_concat. rewrite List.app_nil_r. apply brel_list_reflexive; auto. 
Defined. 

Lemma bop_concat_not_exists_ann: ∀ (S : Type) (r : brel S) (witness : S), 
                  bop_not_exists_ann (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r witness. unfold bop_not_exists_ann. intro a. 
       case_eq(a). 
          intro Q. exists (witness :: nil). left. compute. reflexivity.
          intros s l H. unfold bop_concat. exists (witness :: nil). right. 
             rewrite <- List.app_comm_cons. rewrite List.app_nil_l.
             apply brel_list_not_cons_equal_left. 
Defined. 

Lemma brel_list_cons : ∀ (S : Type) (r : brel S) (a : S) (l1 l2 : list S), 
         brel_reflexive S r -> @brel_list S r (a :: l1) (a :: l2) = @brel_list S r l1 l2. 
Proof. intros S r a l1 l2 refS. unfold brel_list at 1. fold @brel_list. 
       rewrite (refS a). simpl. reflexivity. 
Qed. 

Lemma  bop_concat_left_cancellative : ∀ (S : Type) (r : brel S), 
       brel_reflexive S r -> 
         bop_left_cancellative (list S) (@brel_list S r) (@bop_concat S).
Proof. unfold bop_left_cancellative. intros S r refS. induction s; intros t u H.
       simpl in H. assumption. 
       unfold bop_concat in H. fold @bop_concat in H. 
       rewrite <- List.app_comm_cons in H. rewrite <- List.app_comm_cons in H.  
       rewrite brel_list_cons in H; auto.  
Qed.        

Lemma bop_concat_right_cancellative : ∀ (S : Type) (r : brel S), 
         bop_right_cancellative (list S) (@brel_list S r) (@bop_concat S).
Proof. unfold bop_right_cancellative, bop_concat. 
       intros S r. induction s; induction t; induction u; intro H.
          compute. reflexivity. 
          compute in H. discriminate. 
          compute in H. discriminate. 
          rewrite List.app_nil_r in H.  rewrite List.app_nil_r in H. assumption. 
          compute. reflexivity. 
          compute. simpl in H. apply andb_is_true_left in H. destruct H as [L R].
             rewrite concat_cons_no_left_id in R; auto. 
          compute. simpl in H. apply andb_is_true_left in H. destruct H as [L R].
             rewrite concat_cons_no_left_id_v2 in R; auto.              
          rewrite <- List.app_comm_cons in H. rewrite <- List.app_comm_cons in H.
          unfold brel_list in H. fold @brel_list in H.
          apply andb_is_true_left in H. destruct H as [L R].
          apply IHt in R.
          unfold brel_list. fold @brel_list.
          apply andb_is_true_right; split; auto. 
Qed. 

Lemma  bop_concat_not_left_constant : ∀ (S : Type) (r : brel S) (s : S), 
         bop_not_left_constant (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s . exists (nil, (nil, s :: nil)); simpl. reflexivity. Defined. 

Lemma  bop_concat_not_right_constant : ∀ (S : Type) (r : brel S) (s : S), 
         bop_not_right_constant (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s. exists (nil, (nil, s :: nil)); simpl. reflexivity. Defined. 


Lemma  bop_concat_not_anti_left : ∀ (S : Type) (r : brel S) (s : S), 
         brel_reflexive S r -> bop_not_anti_left (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s refS. exists (s :: nil, nil); simpl. 
       rewrite (refS s). simpl. reflexivity. 
Defined. 


Lemma  bop_concat_not_anti_right : ∀ (S : Type) (r : brel S) (s : S), 
         brel_reflexive S r -> bop_not_anti_right (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s refS. exists (s :: nil, nil); simpl. 
       rewrite (refS s). simpl. reflexivity. 
Defined. 

