Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.combined. 
Require Import CAS.code.uop.

Definition bop_union : ∀ {S : Type}, brel S → binary_op (finite_set S) 
:= λ {S} r,  bop_then_unary (uop_duplicate_elim r) (@bop_concat S).

Require Import CAS.theory.uop_properties. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.brel.subset.
Require Import CAS.theory.brel.add_constant. 
(* Require Import CAS.theory.bop.then_unary. *) 
Require Import CAS.theory.brel.subset.
Require Import CAS.theory.brel.set.
(* Require Import CAS.theory.uop.duplicate_elim. *) 
Require Import CAS.theory.bop.add_ann. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.set.

(* from duplicate elim *)

Lemma  uop_duplicate_elim_lemma_1 : 
   ∀ (S : Type) (eq : brel S) (a b: S),  
     brel_symmetric S eq →
     brel_transitive S eq →
     eq b a = true →
       ∀ (X : finite_set S), in_set eq (uop_duplicate_elim eq (a :: X)) b = true.
Proof. intros S eq a b symS transS E. induction X. 
          compute. rewrite E. reflexivity. 
          simpl. simpl in IHX. 
          case_eq(eq a a0); case_eq(in_set eq X a); case_eq(in_set eq X a0); intros J K M; simpl.
          rewrite K in IHX. assumption. 
          rewrite (transS _ _ _ E M). simpl. reflexivity. 
          apply symS in M.

          assert (A := in_set_right_congruence _ _ symS transS _ _ _ M J). 
          rewrite A in K. discriminate. 
          rewrite (transS _ _ _ E M). simpl. reflexivity.           
          rewrite K in IHX. assumption. 
          case_eq(eq b a0); intro N. simpl. reflexivity. simpl. rewrite K in IHX. assumption. 
          rewrite E. simpl. reflexivity.           rewrite E. simpl. reflexivity. 
Defined.

Lemma uop_duplicate_elim_lemma_2 : 
   ∀ (S : Type) (eq : brel S) (a : S), 
     ∀ (X : finite_set S), 
       in_set eq X a = false → 
           (uop_duplicate_elim eq (a :: X)) = a :: (uop_duplicate_elim eq X).
Proof. intros S eq a X H. simpl. rewrite H. reflexivity. Defined. 


Lemma in_set_uop_duplicate_elim_intro : 
   ∀ (S : Type) (eq : brel S), 
      brel_symmetric S eq →
      brel_transitive S eq →
       ∀ (X : finite_set S) (a : S), 
         in_set eq X a = true →
            in_set eq (uop_duplicate_elim eq X) a = true. 
Proof. intros S eq symS transS. induction X. 
          intros a I. compute in I. discriminate. 
          intros a0 I. 
          case_eq(in_set eq X a); intro H. 
             unfold uop_duplicate_elim. rewrite H. apply IHX. 
             apply in_set_cons_elim in I. destruct I as [I | I].               
                apply (in_set_right_congruence _ _ symS transS _ _ _ I H); auto. assumption. assumption. 

            apply in_set_cons_elim in I. destruct I as [I | I].
               apply uop_duplicate_elim_lemma_1; auto.  
               rewrite (uop_duplicate_elim_lemma_2 S eq a X H). 
               unfold in_set. fold (@in_set S).
               case_eq(eq a0 a); intro J. 
                  simpl. reflexivity.
                  simpl. apply IHX. assumption. assumption. 
Defined. 

Lemma in_set_uop_duplicate_elim_elim : 
   ∀ (S : Type) (eq : brel S), 
       ∀ (X : finite_set S) (a : S), 
         in_set eq (uop_duplicate_elim eq X) a = true →
            in_set eq X a = true.
Proof. intros S eq. induction X. 
          intros a I. compute in I. discriminate. 
          intros a0 I. unfold in_set. fold (@in_set S). 
          case_eq(eq a0 a); intro H; simpl. 
             reflexivity.
             case_eq(in_set eq X a); intro J. 
                 unfold uop_duplicate_elim in I. rewrite J in I. apply IHX. assumption. 
               rewrite (uop_duplicate_elim_lemma_2 S eq a X J) in I. 
                 unfold in_set in I. fold (@in_set S) in I. rewrite H in I. simpl in I. 
                 assert (QED := IHX a0 I). assumption. 
Defined. 


Lemma in_set_dup_elim_intro : ∀ (S : Type) 
                               (r : brel S) 
                               (symS : brel_symmetric S r) 
                               (transS : brel_transitive S r),
     ∀ (X : finite_set S) (t : S), in_set r X t = true → in_set r (uop_duplicate_elim r X) t = true. 
Proof. intros S r symS transS. 
       induction X; intros t H. 
       simpl in H. discriminate. 
       simpl. case_eq(in_set r X a); intro Q.
          unfold in_set in H.  fold (@in_set S) in H.  
          apply orb_is_true_left in H. destruct H as [H | H].
          apply IHX. apply symS in H. apply (in_set_right_congruence S r symS transS a t X H Q). 
          apply IHX. assumption. 
       unfold in_set. fold (@in_set S). 
          unfold in_set in H.  fold (@in_set S) in H.  
          apply orb_is_true_left in H. destruct H as [H | H].
             rewrite H. simpl. reflexivity. 
             rewrite (IHX t H). rewrite orb_comm. simpl. reflexivity. 
Defined. 



Lemma uop_duplicate_elim_congruence_v1 : ∀ (S : Type) 
                                           (r : brel S)
                                           (symS : brel_symmetric S r) 
                                           (transS : brel_transitive S r),  
      uop_congruence_positive (finite_set S) (brel_subset r) (uop_duplicate_elim r).  
Proof. intros S r symS transS. unfold uop_congruence_positive. 
       induction s; intros t H. 
          simpl. reflexivity. 
          unfold uop_duplicate_elim at 1. fold (@uop_duplicate_elim S r). 
          case_eq(in_set r s a); intro Q. 
             apply IHs. unfold brel_subset in H. fold (@brel_subset S) in H. 
                apply andb_is_true_left in H.  destruct H as [H1 H2].  assumption. 
             unfold brel_subset in H. fold (@brel_subset S) in H. 
             unfold brel_subset. fold (@brel_subset S). 
             apply andb_is_true_left in H.  destruct H as [H1 H2].
             apply andb_is_true_right. split. 
                apply in_set_dup_elim_intro; auto. 
                apply IHs; auto. 
Defined. 

Lemma uop_duplicate_elim_congruence_v2 : ∀ (S : Type) 
                                           (r : brel S)
                                           (symS : brel_symmetric S r) 
                                           (transS : brel_transitive S r),  
      uop_congruence_positive (finite_set S) (brel_set r) (uop_duplicate_elim r).  
Proof. intros S r symS transS w u. unfold brel_set. unfold brel_and_sym. intro H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]. 
       apply andb_is_true_right. split. 
         apply uop_duplicate_elim_congruence_v1. assumption. assumption. assumption. 
         apply uop_duplicate_elim_congruence_v1. assumption. assumption. assumption. 
Defined. 


(* naming convention ? *) 

Lemma in_set_lemma3 : 
  ∀ (S : Type) (r : brel S) (symS : brel_symmetric S r) (a : S) (s t : finite_set S), 
    in_set r (s ++ t) a = true -> (in_set r s a = true) + (in_set r t a = true). 
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
    (in_set r s a = true) + (in_set r t a = true) -> (in_set r (s ++ t) a = true). 
Proof. intros S r a. induction s; intros t [H | H]. 
       simpl in H. discriminate. 
       simpl. assumption. 
       unfold in_set in H. fold (@in_set S) in H. rewrite <- List.app_comm_cons.
       unfold in_set. fold (@in_set S). 
       apply orb_is_true_left in H. destruct H as [H | H]. 
          rewrite H. simpl. reflexivity. 
          rewrite (IHs t (inl _ H)). apply orb_comm. 
       rewrite <- List.app_comm_cons. unfold in_set. fold (@in_set S). 
          rewrite (IHs t (inr _ H)). apply orb_comm. 
Defined. 


Lemma bop_concat_subset_congruence : 
   ∀ (S : Type) (r : brel S), 
     brel_reflexive S r -> brel_symmetric S r -> brel_transitive S r -> 
         bop_congruence (finite_set S) (brel_subset r) (@bop_concat S).
Proof. intros S r refS symS transS. unfold bop_congruence, bop_concat. 
       intros s1 s2 t1 t2 J K. 
       assert (Q := brel_subset_elim S r symS transS _ _ J). 
       assert (H := brel_subset_elim S r symS transS _ _ K).
       apply (brel_subset_intro S r refS). intros a L. 
       apply (in_set_lemma4 S r a t1 t2). apply (in_set_lemma3 S r symS) in L. destruct L as [L | L].
          left. rewrite (Q a L). reflexivity. 
          right. rewrite (H a L). reflexivity. 
Defined. 

Lemma bop_concat_set_congruence : 
   ∀ (S : Type) (r : brel S), 
     brel_reflexive S r -> brel_symmetric S r -> brel_transitive S r -> 
     bop_congruence (finite_set S) (brel_set r) (@bop_concat S).
Proof. intros S r refS symS transS. 
       unfold bop_congruence, bop_concat. unfold brel_set. unfold brel_and_sym. 
       intros s1 s2 t1 t2 H J.  
       apply andb_is_true_left in H. apply andb_is_true_left in J. 
       destruct H as [H1 H2]. destruct J as [J1 J2]. apply andb_is_true_right. split. 
          apply (bop_concat_subset_congruence S r refS symS transS s1 s2 t1 t2 H1 J1).
          apply (bop_concat_subset_congruence S r refS symS transS t1 t2 s1 s2 H2 J2).
Defined. 


Lemma uop_duplicate_elim_preserves_left_v1 : ∀ (S : Type) (r : brel S),
      uop_preserves_left_positive (finite_set S) (brel_subset r) (uop_duplicate_elim r).  
Proof. intros S r. unfold uop_preserves_left_positive. 
       induction s; simpl; intros t H. 
          reflexivity. 
          apply andb_is_true_left in H. destruct H as [H1 H2].
          case_eq(in_set r s a); intro Q. 
             apply IHs. assumption. 
             unfold brel_subset. fold (@brel_subset S). rewrite H1, (IHs t H2). simpl. reflexivity. 
Defined. 


Lemma uop_duplicate_elim_preserves_right_v1 : ∀ (S : Type) (r : brel S),
      brel_symmetric S r -> 
      brel_transitive S r -> 
      uop_preserves_right_positive (finite_set S) (brel_subset r) (uop_duplicate_elim r).  
Proof. intros S r symS transS. unfold uop_preserves_right_positive. 
       induction s; simpl; intros t H; auto. 
          apply andb_is_true_left in H. destruct H as [H1 H2].
          rewrite (IHs t H2).  rewrite (in_set_dup_elim_intro S r symS transS t a H1); auto. 
Defined. 



Lemma uop_duplicate_elim_preserves_right_v2 : ∀ (S : Type) (r : brel S),
      brel_symmetric S r -> 
      brel_transitive S r -> 
      uop_preserves_right_positive (finite_set S) (brel_set r) (uop_duplicate_elim r).  
Proof. intros S r symS transS w u. unfold brel_set. unfold brel_and_sym. intro H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]. 
       apply andb_is_true_right. split. 
         apply uop_duplicate_elim_preserves_right_v1; auto. 
         apply uop_duplicate_elim_preserves_left_v1; auto. 
Defined. 


Lemma duplicate_elim_concat_associative : 
    ∀ (S : Type) (r : brel S), 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
         uop_bop_associative (finite_set S) (brel_set r) (uop_duplicate_elim r) (@bop_concat S). 
Proof. intros S r refS symS transS. unfold uop_bop_associative. intros s t v. 
       assert (H : brel_set r (bop_concat (bop_concat s t) v) 
                              (bop_concat (uop_duplicate_elim r (bop_concat s t)) v) = true).
          apply (bop_concat_set_congruence S r refS symS transS 
                 (bop_concat s t) v (uop_duplicate_elim r (bop_concat s t)) v). 
          apply (uop_duplicate_elim_preserves_right_v2 S r symS transS). 
          apply brel_set_reflexive; auto. 
          apply brel_set_reflexive; auto. 
       assert (K : brel_set r (bop_concat s (bop_concat t v)) 
                              (bop_concat s (uop_duplicate_elim r (bop_concat t v))) = true).
          apply (bop_concat_set_congruence S r refS symS transS 
                 s (bop_concat t v) s (uop_duplicate_elim r (bop_concat t v))). 
          apply brel_set_reflexive; auto. 
          apply (uop_duplicate_elim_preserves_right_v2 S r symS transS). 
          apply brel_set_reflexive; auto. 
          unfold bop_concat in *. rewrite List.app_assoc in K.           
          apply brel_set_symmetric in H. 
          apply (brel_set_transitive S r refS symS transS _ _ _ H K). assumption. 
Defined. 


Lemma uop_duplicate_elim_preserves_left_v2 : ∀ (S : Type) (r : brel S),
      brel_symmetric S r -> 
      brel_transitive S r -> 
      uop_preserves_left_positive (finite_set S) (@brel_set S r) (@uop_duplicate_elim S r).  
Proof. intros S r symS transS w u. unfold brel_set. unfold brel_and_sym. intro H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]. 
       apply andb_is_true_right. split. 
         apply uop_duplicate_elim_preserves_left_v1; auto. 
         apply uop_duplicate_elim_preserves_right_v1; auto. 
Defined. 



(* ************** *) 


(* from then_unary *)

Lemma bop_then_unary_congruence : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
           uop_congruence_positive S r u -> 
           bop_congruence S r b -> 
           bop_congruence S r (bop_then_unary u b).
Proof. intros S r u b congU congB. unfold bop_congruence, bop_then_unary.
       intros s1 s2 t1 t2 H Q. apply congU. apply congB.  assumption. assumption. 
Defined. 

Lemma bop_then_unary_associative : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
           uop_congruence_positive S r u -> 
           uop_bop_associative S r u b -> 
           bop_associative S r (@bop_then_unary S u b).
Proof. intros S r u b congS assocS. unfold bop_associative, bop_then_unary.
       intros s t v. apply congS.
       apply assocS. 
Defined. 

(*  How to capture reductions? 

(a)  u (u (s * t) * v) =  u (s * (u (t * v)))

dist? 

  a x (b + c) 
= r(a x r(b + c))
= r(a x (b + c))
= r((a x b) + (a x c))
= r(r(a x b) + r(a x c))
= (a x b) + (a x c) 


(A) u(s * t) = u((u(s) * t) 
(B) u(s * t) = u(s * u(t)) 

Prove (a) : 

  u (u (s * t) * v)
= u ((s * t) * v)
= u (s * (t * v)) 
= u (s * u(t * v)) 

*) 

Lemma bop_then_unary_idempotent : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
         uop_preserves_left_positive S r u -> 
         bop_idempotent S r b -> 
           bop_idempotent S r (@bop_then_unary S u b).
Proof. 
       intros S r u b presS idemS. 
       unfold bop_then_unary. unfold bop_idempotent. 
       intro s. apply (presS (b s s) s). apply idemS. 
Defined. 


Lemma bop_then_unary_commutative : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
         uop_congruence_positive S r u -> 
         bop_commutative S r b -> 
           bop_commutative S r (@bop_then_unary S u b).
Proof. intros S r u b congS commS. 
       intros s t. unfold bop_then_unary. apply congS. apply commS. 
Defined. 

(* ************** *)

Lemma in_set_concat_intro : ∀ (S : Type) (eq : brel S) (X Y : finite_set S) (a : S),
  (in_set eq X a = true) + (in_set eq Y a = true)
  -> 
  in_set eq (X ++ Y) a = true.
Admitted.   

Lemma in_set_concat_elim : ∀ (S : Type) (eq : brel S) (X Y : finite_set S) (a : S),
  in_set eq (X ++ Y) a = true
  -> 
  (in_set eq X a = true) + (in_set eq Y a = true).
Admitted.   

Lemma in_set_bop_union_intro : 
   ∀ (S : Type) (eq : brel S) (X Y : finite_set S) (a : S),
      brel_symmetric S eq →
      brel_transitive S eq →
       (in_set eq X a = true) + (in_set eq Y a = true) →
         in_set eq (bop_union eq X Y) a = true. 
Proof. intros S eq X Y a symS transS H. 
       unfold bop_union. unfold bop_then_unary. unfold bop_concat. 
       apply in_set_uop_duplicate_elim_intro; auto.
       apply in_set_concat_intro; auto. 
Defined. 


Lemma in_set_bop_union_elim : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (X Y : finite_set S) (a : S),
      brel_transitive S eq →
       in_set eq (bop_union eq X Y) a = true  →
       (in_set eq X a = true) + (in_set eq Y a = true). 
Proof. intros S eq lt X Y a transS H. 
       unfold bop_union in H. unfold bop_then_unary in H. unfold bop_concat in H. 
       apply in_set_uop_duplicate_elim_elim in H. 
       apply in_set_concat_elim in H. assumption. 
Defined. 


(* 

Issue with union : If the carrier set S is infinite, 
then the annihilator for union is not a finite set. 
Even if S is a finite set, it can be enormous, with no good way 
of representing it.  Therefore, we define a constructon 
that forces the definition of a new constant representing 
the annihilator. 

The "bop_union_..._raw" results below capture the properties 
of union before the annihilator is added. 

*) 

(* ************************************* raw ************************************* *) 

  
Lemma bop_union_congruence_raw : 
   ∀ (S : Type) (r : brel S), 
     brel_reflexive S r -> brel_symmetric S r -> brel_transitive S r -> 
           bop_congruence (finite_set S) (brel_set r) (bop_union r).
Proof. intros S r refS symS transS. unfold bop_union.
       apply bop_then_unary_congruence. 
       apply uop_duplicate_elim_congruence_v2; auto. 
       apply bop_concat_set_congruence; auto. 
Defined. 


Lemma bop_union_associative_raw : 
   ∀ (S : Type) (r : brel S), 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
         bop_associative (finite_set S) (brel_set r) (bop_union r).
Proof. intros S r refS symS transS. unfold bop_union. 
       apply bop_then_unary_associative. 
       apply uop_duplicate_elim_congruence_v2; auto. 
       apply duplicate_elim_concat_associative; auto. 
Defined.


(* simplify? see below *) 
Lemma subset_cat_left : 
    ∀ (S : Type) (r : brel S) (s v u : finite_set S), 
        brel_subset r u s = true -> 
        brel_subset r v s = true -> 
        brel_subset r (u ++ v) s = true. 
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
                unfold brel_subset. fold (@brel_subset S). unfold in_set. fold (@in_set S). 
                rewrite Q1, Q2. simpl. reflexivity. 
             rewrite H1. simpl. apply IHu. assumption. 
                unfold brel_subset. fold (@brel_subset S). unfold in_set. fold (@in_set S). 
                rewrite Q1, Q2. rewrite orb_comm. simpl. reflexivity. 
             rewrite H1. rewrite orb_comm. simpl.  apply IHu. assumption. 
                unfold brel_subset. fold (@brel_subset S). unfold in_set. fold (@in_set S). 
                rewrite Q1, Q2. simpl. reflexivity. 
             rewrite H1. rewrite orb_comm. simpl.  apply IHu. assumption. 
                unfold brel_subset. fold (@brel_subset S). unfold in_set. fold (@in_set S). 
                rewrite Q1, Q2. rewrite orb_comm. simpl. reflexivity. 
Defined. 



(* simplify? *) 
Lemma subset_cat_right : 
    ∀ (S : Type) (r : brel S) (s v u : finite_set S), 
        brel_subset r s u = true -> 
        brel_subset r s v = true -> 
        brel_subset r s (u ++ v) = true. 
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
             bop_idempotent (finite_set S) (brel_set r) (@bop_concat S).
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


Lemma bop_union_idempotent_raw : 
     ∀ (S : Type) 
       (r : brel S), 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
           bop_idempotent (finite_set S) (brel_set r) (bop_union r).
Proof. intros S r refS symS transS. unfold bop_union.
       apply bop_then_unary_idempotent.
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
     (brel_subset r s t = true) + (brel_subset r s u = true) -> 
     brel_subset r s (t ++ u) = true. 
Proof. intros S r s t u refS symS transS H.             
       apply (brel_subset_intro S r); auto. intros a J. destruct H as [H | H].
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
             bop_commutative (finite_set S) (brel_set r) (@bop_concat S).
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



Lemma bop_union_commutative_raw : 
   ∀ (S : Type) (r : brel S), 
   brel_reflexive S r -> 
   brel_symmetric S r -> 
   brel_transitive S r -> 
           bop_commutative(finite_set S) (brel_set r) (bop_union r).
Proof. intros S r refS symS transS. unfold bop_union.
       apply bop_then_unary_commutative. 
       apply (uop_duplicate_elim_congruence_v2 S r symS transS). 
       apply (bop_concat_set_commutative S r refS symS transS).
Defined.

Lemma bop_union_not_selective_raw : 
   ∀ (S : Type) (r : brel S) (s : S) (f : S -> S), 
   brel_reflexive S r -> 
   brel_symmetric S r -> 
   brel_not_trivial S r f -> 
      bop_not_selective (finite_set S) (brel_set r) (bop_union r).
Proof. intros S r s f refS symS Pf.
       unfold bop_union, bop_not_selective. 
       exists ((s ::nil), ((f s) ::nil)).  
       unfold bop_concat, bop_then_unary.
       rewrite <- List.app_comm_cons.
       rewrite List.app_nil_l. 
       unfold uop_duplicate_elim.
       unfold in_set. 
       destruct (Pf s) as [L R].
       rewrite L; simpl. 
       unfold brel_set.
       unfold brel_and_sym.
       unfold brel_subset. 
       unfold in_set.
       rewrite (symS s), L; simpl.
       rewrite orb_comm. simpl. 
       case_eq(r (f s) s); intro Q. 
          apply symS in Q.
          rewrite L in Q. discriminate.
          auto. 
          apply refS. 
Defined.


Lemma bop_union_nil : ∀ (S : Type) (r : brel S),
     brel_reflexive S r ->
     brel_symmetric S r -> 
     brel_transitive S r -> 
            ∀ (X : finite_set S), brel_set r (bop_union r nil X) X = true. 
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


Lemma bop_union_nil_is_id : ∀ (S : Type) (r : brel S), 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
       bop_is_id (finite_set S) (brel_set r) (bop_union r) nil.
Proof. intros S r refS symS transS s. 
       assert (fact1 : brel_set r (bop_union r nil s) s = true). 
          apply bop_union_nil; auto. 
       assert (fact2 : brel_set r (bop_union r s nil) (bop_union r nil s) = true). 
          apply bop_union_commutative_raw; auto. 
       assert (fact3 : brel_set r (bop_union r s nil) s = true). 
          apply (brel_set_transitive S r refS symS transS _ _ _ fact2 fact1). 
       rewrite fact1, fact3; auto. 
Defined. 
  
  
Lemma bop_union_exists_id_raw : ∀ (S : Type) (r : brel S), 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
         bop_exists_id (finite_set S) (brel_set r) (bop_union r).
Proof. intros S r refS symS transS. exists nil.
       apply bop_union_nil_is_id; auto. 
Defined. 


(* ************************************* raw to cooked ************************************* *) 

Section UnionCooked.

Variable S : Type.
Variable r : brel S.
Variable c : cas_constant.
Variable s : S.
Variable f : S -> S.

Variable nt : brel_not_trivial S r f. 
Variable refS : brel_reflexive S r.
Variable symS : brel_symmetric S r.
Variable transS : brel_transitive S r. 

Lemma bop_union_associative : 
        bop_associative
            (with_constant (finite_set S)) 
            (brel_add_constant (brel_set r) c)
            (bop_add_ann (bop_union r) c). 
Proof. apply bop_add_ann_associative.
       apply bop_union_associative_raw; auto.        
Defined. 


Lemma bop_union_congruence : 
        bop_congruence
            (with_constant (finite_set S)) 
            (brel_add_constant (brel_set r) c)
            (bop_add_ann (bop_union r) c). 
Proof. apply bop_add_ann_congruence. 
       apply bop_union_congruence_raw; auto. 
Defined. 


Lemma bop_union_commutative : 
       bop_commutative
            (with_constant (finite_set S)) 
            (brel_add_constant (brel_set r) c)
            (bop_add_ann (bop_union r) c). 
Proof. apply bop_add_ann_commutative. 
       apply bop_union_commutative_raw; auto. 
Defined. 


Lemma bop_union_idempotent : 
        bop_idempotent
            (with_constant (finite_set S)) 
            (brel_add_constant (brel_set r) c)
            (bop_add_ann (bop_union r) c). 
Proof. apply bop_add_ann_idempotent. 
       apply bop_union_idempotent_raw; auto. 
Defined. 


Lemma bop_union_not_selective : 
        bop_not_selective
            (with_constant (finite_set S)) 
            (brel_add_constant (brel_set r) c)
            (bop_add_ann (bop_union r) c).
Proof. apply bop_add_ann_not_selective.
       apply (bop_union_not_selective_raw S r s f refS symS nt).
Defined. 


Lemma bop_union_exists_id : 
        bop_exists_id
            (with_constant (finite_set S)) 
            (brel_add_constant (brel_set r) c)
            (bop_add_ann (bop_union r) c). 
Proof. apply bop_add_ann_exists_id. 
       apply bop_union_exists_id_raw; auto. 
Defined. 

Lemma bop_union_exists_ann : 
        bop_exists_ann
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bop_add_ann_exists_ann.  Defined. 

(* below are not really needed since we only construct a sg_CI for union *) 

Lemma bop_union_not_is_left : 
        bop_not_is_left
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bop_add_ann_not_is_left. exact (s :: nil). Defined. 


Lemma bop_union_not_is_right : 
        bop_not_is_right
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bop_add_ann_not_is_right. exact (s :: nil). Defined. 


Lemma bop_union_not_left_cancellative : 
        bop_not_left_cancellative
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. assert (NT := brel_set_not_trivial S r s). 
       apply (bop_add_ann_not_left_cancellative _ _ c _ (s :: nil) _  NT). 
Defined. 

Lemma bop_union_not_right_cancellative : 
        bop_not_right_cancellative
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. assert (NT := brel_set_not_trivial S r s). 
       apply (bop_add_ann_not_right_cancellative _ _ c _ (s :: nil) _  NT). 
Defined. 


Lemma bop_union_not_left_constant : 
        bop_not_left_constant
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply (bop_add_ann_not_left_constant _ (brel_set r) c (bop_union r) (s :: nil)). Defined. 

Lemma bop_union_not_right_constant : 
        bop_not_right_constant
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply (bop_add_ann_not_right_constant _ (brel_set r) c (bop_union r) (s :: nil)). Defined. 

Lemma bop_union_not_anti_left : 
        bop_not_anti_left
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply (bop_add_ann_not_anti_left _ (brel_set r) c (bop_union r) (s :: nil)). Defined. 


Lemma bop_union_not_anti_right : 
        bop_not_anti_right
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply (bop_add_ann_not_anti_right _ (brel_set r) c (bop_union r) (s :: nil)). Defined. 

End UnionCooked.