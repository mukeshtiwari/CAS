Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.in_set.
Require Import CAS.theory.brel.subset.
Require Import CAS.theory.brel.set.


Lemma  uop_duplicate_elim_lemma_1 : 
   ∀ (S : Type) (eq : brel S) (a b: S),  
     brel_symmetric S eq →
     brel_transitive S eq →
     eq b a = true →
       ∀ (X : finite_set S), in_set S eq (uop_duplicate_elim S eq (a :: X)) b = true.
Proof. intros S eq a b symS transS E. induction X. 
          compute. rewrite E. reflexivity. 
          simpl. simpl in IHX. 
          case_eq(eq a a0); case_eq(in_set S eq X a); case_eq(in_set S eq X a0); intros J K M; simpl.
          rewrite K in IHX. assumption. 
          rewrite (transS _ _ _ E M). simpl. reflexivity. 
          apply symS in M. 
          assert (A := in_set_right_congruence _ _ symS transS X _ _ M J). 
             rewrite A in K. discriminate. 
          rewrite (transS _ _ _ E M). simpl. reflexivity.           
          rewrite K in IHX. assumption. 
          case_eq(eq b a0); intro N. simpl. reflexivity. simpl. rewrite K in IHX. assumption. 
          rewrite E. simpl. reflexivity.           rewrite E. simpl. reflexivity. 
Defined.  

Lemma uop_duplicate_elim_lemma_2 : 
   ∀ (S : Type) (eq : brel S) (a : S), 
     ∀ (X : finite_set S), 
       in_set S eq X a = false → 
           (uop_duplicate_elim S eq (a :: X)) = a :: (uop_duplicate_elim S eq X).
Proof. intros S eq a X H. simpl. rewrite H. reflexivity. Defined. 


Lemma in_set_uop_duplicate_elim_intro : 
   ∀ (S : Type) (eq : brel S), 
      brel_symmetric S eq →
      brel_transitive S eq →
       ∀ (X : finite_set S) (a : S), 
         in_set S eq X a = true →
            in_set S eq (uop_duplicate_elim S eq X) a = true. 
Proof. intros S eq symS transS. induction X. 
          intros a I. compute in I. discriminate. 
          intros a0 I. 
          case_eq(in_set S eq X a); intro H. 
             unfold uop_duplicate_elim. rewrite H. apply IHX. 
             apply in_set_cons_elim in I. destruct I as [I | I].               
                apply symS in I. 
                apply (in_set_right_congruence _ _ symS transS X _ _ I H). 
                assumption. 
             apply in_set_cons_elim in I. destruct I as [I | I].
               apply uop_duplicate_elim_lemma_1; auto.  
               rewrite (uop_duplicate_elim_lemma_2 S eq a X H). 
               unfold in_set. fold in_set.
               case_eq(eq a0 a); intro J. 
                  simpl. reflexivity.
                  simpl. apply IHX. assumption. 
Defined. 

Lemma in_set_uop_duplicate_elim_elim : 
   ∀ (S : Type) (eq : brel S), 
       ∀ (X : finite_set S) (a : S), 
         in_set S eq (uop_duplicate_elim S eq X) a = true →
            in_set S eq X a = true.
Proof. intros S eq. induction X. 
          intros a I. compute in I. discriminate. 
          intros a0 I. unfold in_set. fold in_set. 
          case_eq(eq a0 a); intro H; simpl. 
             reflexivity.
             case_eq(in_set S eq X a); intro J. 
                 unfold uop_duplicate_elim in I. rewrite J in I. apply IHX. assumption. 
               rewrite (uop_duplicate_elim_lemma_2 S eq a X J) in I. 
                 unfold in_set in I. fold in_set in I. rewrite H in I. simpl in I. 
                 assert (QED := IHX a0 I). assumption. 
Defined. 

Lemma in_set_preserves_right : 
   ∀ (S : Type) (r : brel S), 
        brel_symmetric S r -> 
        brel_transitive S r -> 
            brel2_right_congruence (finite_set S) (S) r (in_set S r). 
Proof. intros S r symS transS. unfold brel2_right_congruence. induction s; intros t1 t2 H Q. 
       simpl in Q. discriminate. 
       unfold in_set in Q. fold in_set in Q. 
       unfold in_set. fold in_set. apply orb_is_true_left in Q. destruct Q as [Q | Q].
          apply symS in H. rewrite (transS t2 t1 a H Q). simpl. reflexivity. 
          rewrite (IHs t1 t2 H Q). rewrite orb_comm. simpl. reflexivity. 
Defined. 


Lemma in_set_dup_elim_true : ∀ (S : Type) 
                               (r : brel S) 
                               (symS : brel_symmetric S r) 
                               (transS : brel_transitive S r),  
     uop_brel2_preserves_left_positive (finite_set S) S (in_set S r) (uop_duplicate_elim S r). 
Proof. intros S r symS transS. unfold uop_brel2_preserves_left_positive. 
       induction s; intros t H. 
       simpl in H. discriminate. 
       simpl. case_eq(in_set S r s a); intro Q.
          unfold in_set in H.  fold in_set in H.  
          apply orb_is_true_left in H. destruct H as [H | H].
          apply IHs. apply symS in H. apply (in_set_preserves_right S r symS transS s a t H Q). 
          apply IHs. assumption. 
       unfold in_set. fold in_set. 
          unfold in_set in H.  fold in_set in H.  
          apply orb_is_true_left in H. destruct H as [H | H].
             rewrite H. simpl. reflexivity. 
             rewrite (IHs t H). rewrite orb_comm. simpl. reflexivity. 
Defined. 



Lemma uop_duplicate_elim_congruence_v1 : ∀ (S : Type) 
                                           (r : brel S)
                                           (symS : brel_symmetric S r) 
                                           (transS : brel_transitive S r),  
      uop_congruence_positive (finite_set S) (brel_subset S r) (uop_duplicate_elim S r).  
Proof. intros S r symS transS. unfold uop_congruence_positive. 
       induction s; intros t H. 
          simpl. reflexivity. 
          unfold uop_duplicate_elim at 1. fold (uop_duplicate_elim S r). 
          case_eq(in_set S r s a); intro Q. 
             apply IHs. unfold brel_subset in H. fold brel_subset in H. 
                apply andb_is_true_left in H.  destruct H as [H1 H2].  assumption. 
             unfold brel_subset in H. fold brel_subset in H. 
             unfold brel_subset. fold brel_subset. 
             apply andb_is_true_left in H.  destruct H as [H1 H2].
             apply andb_is_true_right. split. 
                apply in_set_dup_elim_true. assumption. assumption. assumption. 
                apply IHs. assumption. 
Defined. 


Lemma uop_duplicate_elim_congruence_v2 : ∀ (S : Type) 
                                           (r : brel S)
                                           (symS : brel_symmetric S r) 
                                           (transS : brel_transitive S r),  
      uop_congruence_positive (finite_set S) (brel_set S r) (uop_duplicate_elim S r).  
Proof. intros S r symS transS w u. unfold brel_set. unfold brel_and_sym. intro H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]. 
       apply andb_is_true_right. split. 
         apply uop_duplicate_elim_congruence_v1. assumption. assumption. assumption. 
         apply uop_duplicate_elim_congruence_v1. assumption. assumption. assumption. 
Defined. 



Lemma uop_duplicate_elim_preserves_left_v1 : ∀ (S : Type) (r : brel S),
      uop_preserves_left_positive (finite_set S) (brel_subset S r) (uop_duplicate_elim S r).  
Proof. intros S r. unfold uop_preserves_left_positive. 
       induction s; simpl; intros t H. 
          reflexivity. 
          apply andb_is_true_left in H. destruct H as [H1 H2].
          case_eq(in_set S r s a); intro Q. 
             apply IHs. assumption. 
             unfold brel_subset. fold brel_subset. rewrite H1, (IHs t H2). simpl. reflexivity. 
Defined. 


Lemma uop_duplicate_elim_preserves_right_v1 : ∀ (S : Type) (r : brel S),
      brel_symmetric S r -> 
      brel_transitive S r -> 
      uop_preserves_right_positive (finite_set S) (brel_subset S r) (uop_duplicate_elim S r).  
Proof. intros S r symS transS. unfold uop_preserves_right_positive. 
       induction s; simpl; intros t H. 
          reflexivity. 
          apply andb_is_true_left in H. destruct H as [H1 H2].
          rewrite (IHs t H2).  rewrite (in_set_dup_elim_true S r symS transS t a H1).
          simpl. reflexivity. 
Defined. 



Lemma uop_duplicate_elim_preserves_right_v2 : ∀ (S : Type) (r : brel S),
      brel_symmetric S r -> 
      brel_transitive S r -> 
      uop_preserves_right_positive (finite_set S) (brel_set S r) (uop_duplicate_elim S r).  
Proof. intros S r symS transS w u. unfold brel_set. unfold brel_and_sym. intro H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]. 
       apply andb_is_true_right. split. 
         apply uop_duplicate_elim_preserves_right_v1; auto. 
         apply uop_duplicate_elim_preserves_left_v1; auto. 
Defined. 


(* naming convention ? *) 

Lemma in_set_lemma3 : 
  ∀ (S : Type) (r : brel S) (symS : brel_symmetric S r) (a : S) (s t : finite_set S), 
    in_set S r (s ++ t) a = true -> (in_set S r s a = true) + (in_set S r t a = true). 
Proof. intros S r symS a. induction s; simpl; intros t H. 
          right. assumption. 
          apply orb_is_true_left in H.  destruct H as [H | H].
             rewrite H. simpl. left. reflexivity. 
             destruct (IHs t H) as [Q | Q].
                left. rewrite Q. rewrite orb_comm. simpl. reflexivity. 
                right. assumption. 
Defined. 



Lemma in_set_lemma4 : 
  ∀ (S : Type) (r : brel S) (a : S) (s t : finite_set S), 
    (in_set S r s a = true) + (in_set S r t a = true) -> (in_set S r (s ++ t) a = true). 
Proof. intros S r a. induction s; intros t [H | H]. 
       simpl in H. discriminate. 
       simpl. assumption. 
       unfold in_set in H. fold in_set in H. rewrite <- List.app_comm_cons.
       unfold in_set. fold in_set. 
       apply orb_is_true_left in H. destruct H as [H | H]. 
          rewrite H. simpl. reflexivity. 
          rewrite (IHs t (inl _ H)). apply orb_comm. 
       rewrite <- List.app_comm_cons. unfold in_set. fold in_set. 
          rewrite (IHs t (inr _ H)). apply orb_comm. 
Defined. 


Lemma bop_concat_subset_congruence : 
   ∀ (S : Type) (r : brel S), 
     brel_reflexive S r -> brel_symmetric S r -> brel_transitive S r -> 
         bop_congruence (finite_set S) (brel_subset S r) (bop_concat S).
Proof. intros S r refS symS transS. unfold bop_congruence, bop_concat. 
       intros s1 s2 t1 t2 J K. 
       assert (Q := brel_subset_elim S r symS transS _ _ J). 
       assert (H := brel_subset_elim S r symS transS _ _ K). 
       apply (brel_subset_intro S r refS symS transS). intros a L. 
       apply (in_set_lemma4 S r a t1 t2). apply (in_set_lemma3 S r symS) in L. destruct L as [L | L].
          left. rewrite (Q a L). reflexivity. 
          right. rewrite (H a L). reflexivity. 
Defined. 

Lemma bop_concat_set_congruence : 
   ∀ (S : Type) (r : brel S), 
     brel_reflexive S r -> brel_symmetric S r -> brel_transitive S r -> 
     bop_congruence (finite_set S) (brel_set S r) (bop_concat S).
Proof. intros S r refS symS transS. 
       unfold bop_congruence, bop_concat. unfold brel_set. unfold brel_and_sym. 
       intros s1 s2 t1 t2 H J.  
       apply andb_is_true_left in H. apply andb_is_true_left in J. 
       destruct H as [H1 H2]. destruct J as [J1 J2]. apply andb_is_true_right. split. 
          apply (bop_concat_subset_congruence S r refS symS transS s1 s2 t1 t2 H1 J1).
          apply (bop_concat_subset_congruence S r refS symS transS t1 t2 s1 s2 H2 J2).
Defined. 



Lemma duplicate_elim_concat_associative : 
    ∀ (S : Type) (r : brel S), 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
         uop_bop_associative (finite_set S) (brel_set S r) (uop_duplicate_elim S r) (bop_concat S). 
Proof. intros S r refS symS transS. unfold uop_bop_associative. intros s t v. 
       assert (H : brel_set S r (bop_concat S (bop_concat S s t) v) 
                                (bop_concat S (uop_duplicate_elim S r (bop_concat S s t)) v) = true).
          apply (bop_concat_set_congruence S r refS symS transS 
                 (bop_concat S s t) v (uop_duplicate_elim S r (bop_concat S s t)) v). 
          apply (uop_duplicate_elim_preserves_right_v2 S r symS transS). 
          apply brel_set_reflexive; auto. 
          apply brel_set_reflexive; auto. 
       assert (K : brel_set S r (bop_concat S s (bop_concat S t v)) 
                                (bop_concat S s (uop_duplicate_elim S r (bop_concat S t v))) = true).
          apply (bop_concat_set_congruence S r refS symS transS 
                 s (bop_concat S t v) s (uop_duplicate_elim S r (bop_concat S t v))). 
          apply brel_set_reflexive; auto. 
          apply (uop_duplicate_elim_preserves_right_v2 S r symS transS). 
          apply brel_set_reflexive; auto. 
          unfold bop_concat in *. rewrite List.app_assoc in K.           
          apply brel_set_symmetric in H. 
          apply (brel_set_transitive S r refS symS transS _ _ _ H K). assumption. 
Defined. 



(* What is this?? 

   (S T: Type) (r brel T) (r2 : brel2 T S ), 
           r2 t1 s = true -> r2 t2 a = false -> r t1 t2 = false
*) 
Lemma in_set_subset_false : ∀ (S : Type) (r : brel S), 
           brel_symmetric S r -> 
           brel_transitive S r -> 
           ∀ (a : S) (s t : finite_set S),
           in_set S r s a = true -> 
           in_set S r t a = false -> 
             brel_subset S r s t = false. 
Proof. intros S r symS transS a s t H Q. 
       case_eq(brel_subset S r s t); intro K. 
       assert (J : ∀ a0:S, in_set S r s a0 = true -> in_set S r t a0 = true). 
           apply (brel_subset_elim S r symS transS s t). assumption. 
       rewrite (J a H) in Q. assumption. 
       reflexivity. 
Defined. 

Lemma in_set_dup_elim_false : ∀ (S : Type) 
                               (r : brel S) 
                               (symS : brel_symmetric S r) 
                               (transS : brel_transitive S r),  
     uop_brel2_preserves_left_negative (finite_set S) S (in_set S r) (uop_duplicate_elim S r). 
Proof. intros S r symS transS. unfold uop_brel2_preserves_left_negative. 
       induction s; intros t H. 
       simpl. reflexivity. 
       unfold in_set in H.  fold in_set in H. apply orb_is_false_left in H. destruct H as [H1 H2].
       unfold uop_duplicate_elim. 
       case_eq(in_set S r s a); intro Q. 
          apply IHs. assumption. 
          unfold in_set. rewrite H1. simpl. fold in_set. apply IHs. assumption. 
Defined. 


Lemma uop_duplicate_elim_congruence_false_v1 : ∀ (S : Type) 
                                                 (r : brel S)
                                                 (symS : brel_symmetric S r) 
                                                 (transS : brel_transitive S r),  
      uop_congruence_negative (finite_set S) (brel_subset S r) (uop_duplicate_elim S r).  
Proof. intros S r symS transS. unfold uop_congruence_negative. 
       induction s; intros t H. 
          simpl in H. discriminate. 
          unfold uop_duplicate_elim at 1. fold (uop_duplicate_elim S r). 
          case_eq(in_set S r s a); intro Q. 
             apply IHs. unfold brel_subset in H. fold brel_subset in H. 
                apply andb_is_false_left in H.  destruct H as [H | H].  
                  apply (in_set_subset_false S r symS transS a s t Q H). 
                assumption. 
             unfold brel_subset. fold brel_subset. 
             apply andb_is_false_right. 
             unfold brel_subset in H. fold brel_subset in H. 
             apply andb_is_false_left in H.  destruct H as [H | H].  
                left. apply in_set_dup_elim_false.  assumption. assumption. assumption. 
                right. apply IHs. assumption.  
Defined.


Lemma uop_duplicate_elim_congruence_false_v2 : ∀ (S : Type) 
                                                 (r : brel S)
                                                 (symS : brel_symmetric S r) 
                                                 (transS : brel_transitive S r),  
      uop_congruence_negative (finite_set S) (brel_set S r) (uop_duplicate_elim S r).  
Proof. intros S r symS transS w u. unfold brel_set. unfold brel_and_sym. intro H. 
       apply andb_is_false_right. 
       apply andb_is_false_left in H. destruct H as [H | H]. 
         left. apply uop_duplicate_elim_congruence_false_v1. assumption. assumption. assumption. 
         right. apply uop_duplicate_elim_congruence_false_v1. assumption. assumption. assumption. 
Defined. 


Lemma uop_duplicate_elim_preserves_left_false_v1 : ∀ (S : Type) (r : brel S),
      brel_symmetric S r -> 
      brel_transitive S r -> 
      uop_preserves_left_negative (finite_set S) (brel_subset S r) (uop_duplicate_elim S r).  
Proof. intros S r symS transS. unfold uop_preserves_left_negative. 
       induction s; simpl; intros t H. 
          assumption. 
          apply andb_is_false_left in H. 
          case_eq(in_set S r s a); intro Q; destruct H as [H | H].
             apply (IHs t (in_set_subset_false S r symS transS a s t Q H)). 
             apply (IHs t H). 
             unfold brel_subset. fold brel_subset. rewrite H. simpl. reflexivity. 
             unfold brel_subset. fold brel_subset. rewrite (IHs t H). rewrite andb_comm. simpl. reflexivity. 
Defined. 


Lemma uop_duplicate_elim_preserves_right_false_v1 : ∀ (S : Type) (r : brel S),
      brel_symmetric S r -> 
      brel_transitive S r -> 
      uop_preserves_right_negative (finite_set S) (brel_subset S r) (uop_duplicate_elim S r).  
Proof. intros S r symS transS. unfold uop_preserves_right_negative. 
       induction s; simpl; intros t H. 
          assumption. 
          apply andb_is_false_right. 
          apply andb_is_false_left in H. destruct H as [H | H].
             left. apply (in_set_dup_elim_false S r symS transS t a H). 
             right. apply IHs. assumption. 
Defined. 

(*
*) 

Lemma uop_duplicate_elim_preserves_left_v2 : ∀ (S : Type) (r : brel S),
      brel_symmetric S r -> 
      brel_transitive S r -> 
      uop_preserves_left_positive (finite_set S) (brel_set S r) (uop_duplicate_elim S r).  
Proof. intros S r symS transS w u. unfold brel_set. unfold brel_and_sym. intro H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]. 
       apply andb_is_true_right. split. 
         apply uop_duplicate_elim_preserves_left_v1. assumption. 
         apply uop_duplicate_elim_preserves_right_v1. assumption. assumption. assumption.  
Defined. 


Lemma uop_duplicate_elim_preserves_brel_set : ∀ (S : Type) (r : brel S),
      brel_reflexive _ r →
      brel_symmetric S r -> 
      brel_transitive S r -> 
         uop_preserves_brel (finite_set S) (uop_duplicate_elim S r) (brel_set S r). 
Proof. intros S r refS symS transS X. 
       assert (T := brel_set_reflexive S r refS symS transS). 
       apply (uop_duplicate_elim_preserves_left_v2 S r symS transS X X (T X)). 
Defined. 





