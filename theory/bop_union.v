Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.uop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.brel_and_sym. 
Require Import CAS.theory.bop_then_unary. 
Require Import CAS.theory.bop_intersect. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel2_in_set.
Require Import CAS.theory.brel_subset.
Require Import CAS.theory.brel_set.
Require Import CAS.theory.uop_duplicate_elim. 


Lemma in_set_bop_union_intro : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (X Y : finite_set S) (a : S),
      brel_symmetric S eq →
      brel_transitive S eq →
       (in_set S eq X a = true) + (in_set S eq Y a = true) →
         in_set S eq (bop_union S eq X Y) a = true. 
Proof. intros S eq lt X Y a symS transS H. 
       unfold bop_union. unfold bop_then_unary. unfold bop_concat. 
       apply in_set_uop_duplicate_elim_intro; auto.
       apply in_set_concat_intro. 
       destruct H as [L | R]. left. assumption. right. assumption. 
Defined. 


Lemma in_set_bop_union_elim : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (X Y : finite_set S) (a : S),
      brel_transitive S eq →
       in_set S eq (bop_union S eq X Y) a = true  →
       (in_set S eq X a = true) + (in_set S eq Y a = true). 
Proof. intros S eq lt X Y a transS H. 
       unfold bop_union in H. unfold bop_then_unary in H. unfold bop_concat in H. 
       apply in_set_uop_duplicate_elim_elim in H. 
       apply in_set_concat_elim in H. assumption. 
Defined. 


(* semigroup properties *) 

Lemma bop_union_congruence : 
   ∀ (S : Type) (r : brel S), 
     brel_reflexive S r -> brel_symmetric S r -> brel_transitive S r -> 
           bop_congruence (finite_set S) (brel_set S r) (bop_union S r).
Proof. intros S r refS symS transS. unfold bop_union. apply bop_then_unary_congruence. 
       apply (uop_duplicate_elim_congruence_v2 S r symS transS). 
       apply (bop_concat_set_congruence S r refS symS transS). 
Defined. 


Lemma bop_union_associative : 
   ∀ (S : Type) (r : brel S), 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
         bop_associative (finite_set S) (brel_set S r) (bop_union S r).
Proof. intros S r refS symS transS. unfold bop_union. 
       apply bop_then_unary_associative. 
       apply uop_duplicate_elim_congruence_v2; auto. 
       apply duplicate_elim_concat_associative; auto. 
Defined.


(* simplify? see below *) 
Lemma subset_cat_left : 
    ∀ (S : Type) (r : brel S) (s v u : finite_set S), 
        brel_subset S r u s = true -> 
        brel_subset S r v s = true -> 
        brel_subset S r (u ++ v) s = true. 
Proof. intros S r. induction s; induction v; induction u; simpl; intros H Q. 
       reflexivity. assumption. assumption. assumption. assumption. 
       apply andb_is_true_left in H. destruct H as [H1 H2].
          apply orb_is_true_left in H1. destruct H1 as [H1 | H1].
             rewrite H1. simpl. apply IHu. assumption. simpl. reflexivity. 
             rewrite List.app_nil_r. rewrite H1, H2. rewrite orb_comm. simpl. reflexivity. 
       apply andb_is_true_left in Q. destruct Q as [Q1 Q2].      
          apply orb_is_true_left in Q1. destruct Q1 as [Q1 | Q1]. 
             rewrite Q1. simpl. assumption. 
             rewrite Q1, Q2. rewrite orb_comm. simpl. reflexivity. 
       apply andb_is_true_left in H. apply andb_is_true_left in Q. 
          destruct H as [H1 H2]. destruct Q as [Q1 Q2].
          apply orb_is_true_left in H1.  apply orb_is_true_left in Q1. 
          destruct H1 as [H1 | H1]; destruct Q1 as [Q1 | Q1]. 
             rewrite H1. simpl. apply IHu. assumption. 
                unfold brel_subset. fold brel_subset. unfold in_set. fold in_set. 
                rewrite Q1, Q2. simpl. reflexivity. 
             rewrite H1. simpl. apply IHu. assumption. 
                unfold brel_subset. fold brel_subset. unfold in_set. fold in_set. 
                rewrite Q1, Q2. rewrite orb_comm. simpl. reflexivity. 
             rewrite H1. rewrite orb_comm. simpl.  apply IHu. assumption. 
                unfold brel_subset. fold brel_subset. unfold in_set. fold in_set. 
                rewrite Q1, Q2. simpl. reflexivity. 
             rewrite H1. rewrite orb_comm. simpl.  apply IHu. assumption. 
                unfold brel_subset. fold brel_subset. unfold in_set. fold in_set. 
                rewrite Q1, Q2. rewrite orb_comm. simpl. reflexivity. 
Defined. 



(* simplify? *) 
Lemma subset_cat_right : 
    ∀ (S : Type) (r : brel S) (s v u : finite_set S), 
        brel_subset S r s u = true -> 
        brel_subset S r s v = true -> 
        brel_subset S r s (u ++ v) = true. 
Proof. intros S r. induction s; induction v; induction u; simpl; intros H Q. 
       reflexivity. assumption. assumption. assumption. assumption. 
       apply andb_is_true_left in H. destruct H as [H1 H2].
          apply orb_is_true_left in H1. destruct H1 as [H1 | H1].
             rewrite H1. simpl. rewrite List.app_nil_r. assumption. 
             rewrite List.app_nil_r. rewrite H1, H2. rewrite orb_comm. simpl. reflexivity. 
       apply andb_is_true_left in Q. destruct Q as [Q1 Q2].      
          apply orb_is_true_left in Q1. destruct Q1 as [Q1 | Q1]. 
             rewrite Q1. simpl. assumption. 
             rewrite Q1, Q2. rewrite orb_comm. simpl. reflexivity. 
       apply andb_is_true_left in H. apply andb_is_true_left in Q. 
          destruct H as [H1 H2]. destruct Q as [Q1 Q2].
          apply orb_is_true_left in H1.  apply orb_is_true_left in Q1. 
          destruct H1 as [H1 | H1]; destruct Q1 as [Q1 | Q1]. 
             rewrite H1. simpl. apply (IHs (a0 :: v) (a1 :: u) H2 Q2). 
             rewrite H1. simpl. apply (IHs (a0 :: v) (a1 :: u) H2 Q2). 
             rewrite List.app_comm_cons. rewrite (IHs (a0 :: v) (a1 :: u) H2 Q2). 
                rewrite (in_set_lemma4 S r a u (a0 :: v) (inl _ H1)). 
                rewrite orb_comm. simpl. reflexivity. 
             rewrite (in_set_lemma4 S r a u (a0 :: v) (inl _ H1)). 
                rewrite orb_comm. simpl. apply (IHs (a0 :: v) (a1 :: u) H2 Q2). 
Defined. 



Lemma bop_concat_set_idempotent : 
     ∀ (S : Type) 
       (r : brel S), 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
             bop_idempotent (finite_set S) (brel_set S r) (bop_concat S).
Proof.  intros S r refS symS transS. unfold bop_idempotent, bop_concat.
        intro s. unfold brel_set. unfold brel_and_sym. 
        apply andb_is_true_right. split. 
          apply subset_cat_left.  
                apply brel_subset_reflexive; auto. 
                apply brel_subset_reflexive; auto. 
          apply subset_cat_right.  
                apply brel_subset_reflexive; auto. 
                apply brel_subset_reflexive; auto. 
Defined. 



Lemma bop_union_idempotent : 
     ∀ (S : Type) 
       (r : brel S), 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
           bop_idempotent (finite_set S) (brel_set S r) (bop_union S r).
Proof. intros S r refS symS transS. unfold bop_union. apply bop_then_unary_idempotent.
       apply uop_duplicate_elim_preserves_left_v2; auto. 
       apply bop_concat_set_idempotent; auto. 
Defined. 


(* what is this ? 

   (r s t) + (r s u) -> r s (b t u) 

*) 

Lemma tmp : ∀ (S : Type) (r : brel S) (s t u : finite_set S), 
     brel_reflexive S r -> 
     brel_symmetric S r -> 
     brel_transitive S r -> 
     (brel_subset S r s t = true) + (brel_subset S r s u = true) -> 
     brel_subset S r s (t ++ u) = true. 
Proof. intros S r s t u refS symS transS H.             
       apply (brel_subset_intro S r refS symS transS). intros a J. destruct H as [H | H].
          assert (Q := brel_subset_elim S r symS transS s t H). 
            rewrite (in_set_lemma4 S r a t u (inl _ (Q a J))). reflexivity. 
          assert (Q := brel_subset_elim S r symS transS s u H). 
            rewrite (in_set_lemma4 S r a t u (inr _ (Q a J))). reflexivity. 
Defined. 

(* naming convension? *) 
Lemma bop_concat_set_commutative : 
     ∀ (S : Type) 
       (r : brel S), 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
             bop_commutative (finite_set S) (brel_set S r) (bop_concat S).
Proof.  intros S r refS symS transS. unfold bop_commutative, bop_concat.
        intros s t. unfold brel_set. unfold brel_and_sym. 
        apply andb_is_true_right. split. 
          apply subset_cat_left.  apply (tmp S r _ _ _ refS symS transS). 
             right. apply brel_subset_reflexive; auto. 
             apply (tmp S r _ _ _ refS symS transS). 
             left. apply brel_subset_reflexive; auto. 
          apply subset_cat_left.  apply (tmp S r _ _ _ refS symS transS).
             right. apply brel_subset_reflexive; auto. 
             apply (tmp S r _ _ _ refS symS transS). 
             left. apply brel_subset_reflexive; auto. 
Defined. 



Lemma bop_union_commutative : 
   ∀ (S : Type) (r : brel S), 
   brel_reflexive S r -> 
   brel_symmetric S r -> 
   brel_transitive S r -> 
           bop_commutative(finite_set S) (brel_set S r) (bop_union S r).
Proof. intros S r refS symS transS. unfold bop_union. apply bop_then_unary_commutative. 
       apply (uop_duplicate_elim_congruence_v2 S r symS transS). 
       apply (bop_concat_set_commutative S r refS symS transS).
Defined.

Lemma bop_union_not_selective : 
   ∀ (S : Type) (r : brel S), 
   brel_reflexive S r -> 
   brel_symmetric S r -> 
   brel_nontrivial S r -> 
      bop_not_selective (finite_set S) (brel_set S r) (bop_union S r).
Proof. intros S r refS symS ntS. unfold bop_union, bop_not_selective. 
       destruct (brel_nontrivial_witness _ _ ntS) as [s Ps].
       destruct (brel_nontrivial_negate _ _ ntS) as [f Pf].
       exists ((s ::nil), ((f s) ::nil)). 
       unfold bop_concat, bop_then_unary. rewrite <- List.app_comm_cons. rewrite List.app_nil_l. 
       unfold uop_duplicate_elim. unfold in_set. 
       destruct (Pf s) as [L R]. rewrite L. simpl. 
       unfold brel_set. unfold brel_and_sym. unfold brel_subset. 
       unfold in_set. rewrite (symS s), L. simpl. rewrite orb_comm. simpl. 
       case_eq(r (f s) s); intro Q. 
          apply symS in Q. rewrite L in Q. discriminate.
             simpl. split. reflexivity. reflexivity. 
          apply refS. 
Defined.


Lemma bop_union_not_is_left : ∀ (S : Type) (r : brel S), 
      (brel_witness S r) -> bop_not_is_left (finite_set S) (brel_set S r) (bop_union S r).
Proof. intros S r [s1 _]. unfold bop_union, bop_not_is_left. 
       unfold bop_concat, bop_then_unary. 
       exists (nil, s1 :: nil). rewrite List.app_nil_l. simpl. 
       unfold brel_set. unfold brel_and_sym. apply andb_is_false_right. left. 
          simpl. reflexivity. 
Defined. 


Lemma bop_union_not_is_right : ∀ (S : Type) (r : brel S), 
      (brel_witness S r) -> bop_not_is_right (finite_set S) (brel_set S r) (bop_union S r).
Proof. intros S r [s1 _]. unfold bop_union, bop_not_is_right. 
       unfold bop_concat, bop_then_unary. 
       exists (s1 :: nil, nil). rewrite List.app_nil_r. simpl. 
       unfold brel_set. unfold brel_and_sym. apply andb_is_false_right. left. 
          simpl. reflexivity. 
Defined. 



Lemma bop_union_nil : ∀ (S : Type) (r : brel S),
     brel_reflexive S r ->
     brel_symmetric S r -> 
     brel_transitive S r -> 
            ∀ (X : finite_set S), brel_set S r (bop_union S r nil X) X = true. 
Proof. intros S r refS symS transS X. 
       apply brel_set_intro. split. 
       apply brel_subset_intro; auto. 
       intros a H. apply in_set_bop_union_elim in H; auto. 
       destruct H as [H | H]. 
          unfold in_set in H. discriminate. 
          assumption. 
       apply brel_subset_intro; auto. 
       intros a H. apply in_set_bop_union_intro; auto. 
Defined. 

Lemma bop_union_exists_id : ∀ (S : Type) (r : brel S), 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
         bop_exists_id (finite_set S) (brel_set S r) (bop_union S r).
Proof. intros S r refS symS transS. exists nil. intro s. 
       assert (fact1 : brel_set S r (bop_union S r nil s) s = true). 
          apply bop_union_nil; auto. 
       assert (fact2 : brel_set S r (bop_union S r s nil) (bop_union S r nil s) = true). 
          apply bop_union_commutative; auto. 
       assert (fact3 : brel_set S r (bop_union S r s nil) s = true). 
          apply (brel_set_transitive S r refS symS transS _ _ _ fact2 fact1). 
       rewrite fact1, fact3; auto. 
Defined. 

Lemma bop_union_not_left_cancellative : ∀ (S : Type) (r : brel S), 
      brel_nontrivial S r -> 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
         bop_not_left_cancellative (finite_set S) (brel_set S r) (bop_union S r).
Proof. intros S r [[s sP] [f fP]] refS symS transS. destruct (fP s) as [L R]. 
       exists (s :: (f s) :: nil, (s :: nil, (f s) :: nil)); simpl. split. 
          apply brel_set_intro_prop; auto.  split. 
             intros a H. apply in_set_bop_union_intro; auto.  
             apply in_set_bop_union_elim in H; auto.  destruct H as [H | H]. 
                left. assumption. 
                left. compute in H. 
                case_eq(r a s); intro J. 
                   unfold in_set. rewrite J. simpl. reflexivity. 
                   rewrite J in H. discriminate.              
             intros a H. apply in_set_bop_union_intro; auto.  
             apply in_set_bop_union_elim in H; auto.  destruct H as [H | H]. 
                left. assumption. 
                left. compute in H. 
                case_eq(r a (f s)); intro J. 
                   unfold in_set. rewrite J. simpl. apply orb_comm. 
                   rewrite J in H. discriminate.              
          compute. rewrite L. reflexivity. 
Defined. 

Lemma bop_union_not_right_cancellative : ∀ (S : Type) (r : brel S), 
      brel_nontrivial S r -> 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
         bop_not_right_cancellative (finite_set S) (brel_set S r) (bop_union S r).
Proof. intros S r [[s sP] [f fP]] refS symS transS. destruct (fP s) as [L R]. 
       exists (s :: (f s) :: nil, (s :: nil, (f s) :: nil)); simpl. split. 
          apply brel_set_intro_prop; auto.  split. 
             intros a H. apply in_set_bop_union_intro; auto.  
             apply in_set_bop_union_elim in H; auto.  destruct H as [H | H]. 
                right. compute in H.  
                case_eq(r a s); intro J. 
                   unfold in_set. rewrite J. simpl. reflexivity. 
                   rewrite J in H. discriminate.              
                right. assumption. 
             intros a H. apply in_set_bop_union_intro; auto.  
             apply in_set_bop_union_elim in H; auto.  destruct H as [H | H]. 
                right. compute in H.  
                case_eq(r a (f s)); intro J. 
                   unfold in_set. rewrite J. simpl. apply orb_comm. 
                   rewrite J in H. discriminate.              
                right. assumption. 
          compute. rewrite L. reflexivity. 
Defined. 

Lemma bop_union_not_left_constant : ∀ (S : Type) (r : brel S), 
       brel_nontrivial S r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
          bop_not_left_constant (finite_set S) (brel_set S r) (bop_union S r).
Proof. intros S r [[s sP] [f fP]] refS symS transS. destruct (fP s) as [L R]. 
       exists (nil, (s :: nil, (f s) :: nil)); compute. 
       rewrite L. reflexivity. 
Defined. 


Lemma bop_union_not_right_constant : ∀ (S : Type) (r : brel S), 
       brel_nontrivial S r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
          bop_not_right_constant (finite_set S) (brel_set S r) (bop_union S r).
Proof. intros S r [[s sP] [f fP]] refS symS transS. destruct (fP s) as [L R]. 
       exists (nil, (s :: nil, (f s) :: nil)); compute. 
       rewrite L. reflexivity. 
Defined. 
