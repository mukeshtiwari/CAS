Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.theory.set. 

Require Import CAS.coq.uop.properties.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.set.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.  
Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.or.

Require Import CAS.coq.po.dual. 
Require Import CAS.coq.os.properties. 

Section Computation.

Definition bop_union : ∀ {S : Type}, brel S → binary_op (finite_set S) 
  := λ {S} r X Y,  uop_duplicate_elim r (bop_concat X Y).

End Computation.   


Section Theory.


Section Concat.
  Variable S: Type.
  Variable r : brel S.
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.
Lemma bop_concat_subset_congruence : bop_congruence (finite_set S) (brel_subset r) (@bop_concat S).
Proof. unfold bop_congruence, bop_concat. 
       intros s1 s2 t1 t2 J K. 
       assert (Q := brel_subset_elim S r symS tranS _ _ J). 
       assert (H := brel_subset_elim S r symS tranS _ _ K).
       apply (brel_subset_intro S r refS). intros a L. 
       apply (in_set_concat_intro S r t1 t2). apply (in_set_concat_elim S r symS) in L. destruct L as [L | L].
          left. rewrite (Q a L). reflexivity. 
          right. rewrite (H a L). reflexivity. 
Defined. 


Lemma bop_concat_set_congruence : bop_congruence (finite_set S) (brel_set r) (@bop_concat S).
Proof. unfold bop_congruence, bop_concat. unfold brel_set. unfold brel_and_sym. 
       intros s1 s2 t1 t2 H J.  
       apply bop_and_elim in H. apply bop_and_elim in J. 
       destruct H as [H1 H2]. destruct J as [J1 J2]. apply bop_and_intro. 
          apply (bop_concat_subset_congruence s1 s2 t1 t2 H1 J1).
          apply (bop_concat_subset_congruence t1 t2 s1 s2 H2 J2).
Defined. 
  

(* what is this ? 

   (r s t) + (r s u) -> r s (b t u) 

*) 

Lemma brel_subset_concat_right_intro  : ∀ (s t u : finite_set S), 
     (brel_subset r s t = true) + (brel_subset r s u = true) -> 
     brel_subset r s (t ++ u) = true. 
Proof. intros s t u H.             
       apply (brel_subset_intro S r); auto.
       intros a J. destruct H as [H | H].
       apply in_set_concat_intro.
       assert (Q := brel_subset_elim S r symS tranS s t H).
       left. apply Q; auto.
       assert (Q := brel_subset_elim S r symS tranS s u H).        
       apply in_set_concat_intro.
       right. apply Q; auto.
Defined. 



(* simplify? see below *) 
Lemma subset_cat_left : 
    ∀ (s v u : finite_set S), 
        brel_subset r u s = true -> 
        brel_subset r v s = true -> 
        brel_subset r (u ++ v) s = true. 
Proof. induction s; induction v; induction u; simpl; intros H Q. 
       reflexivity. assumption. assumption. assumption. assumption. 
       apply bop_and_elim in H. destruct H as [H1 H2].
          apply bop_or_elim in H1. destruct H1 as [H1 | H1].
             rewrite H1. simpl. apply IHu. assumption. simpl. reflexivity. 
             rewrite List.app_nil_r. rewrite H1, H2. rewrite orb_comm. simpl. reflexivity. 
       apply bop_and_elim in Q. destruct Q as [Q1 Q2].      
          apply bop_or_elim in Q1. destruct Q1 as [Q1 | Q1]. 
             rewrite Q1. simpl. assumption. 
             rewrite Q1, Q2. rewrite orb_comm. simpl. reflexivity. 
       apply bop_and_elim in H. apply bop_and_elim in Q. 
          destruct H as [H1 H2]. destruct Q as [Q1 Q2].
          apply bop_or_elim in H1.  apply bop_or_elim in Q1. 
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
  ∀ (s v u : finite_set S),
        brel_subset r s u = true -> 
        brel_subset r s v = true -> 
        brel_subset r s (u ++ v) = true. 
Proof. induction s; induction v; induction u; simpl; intros H Q. 
       reflexivity. assumption. assumption. assumption. assumption. 
       apply bop_and_elim in H. destruct H as [H1 H2].
          apply bop_or_elim in H1. destruct H1 as [H1 | H1].
             rewrite H1. simpl. rewrite List.app_nil_r. assumption. 
             rewrite List.app_nil_r. rewrite H1, H2. rewrite orb_comm. simpl. reflexivity. 
       apply bop_and_elim in Q. destruct Q as [Q1 Q2].      
          apply bop_or_elim in Q1. destruct Q1 as [Q1 | Q1]. 
             rewrite Q1. simpl. assumption. 
             rewrite Q1, Q2. rewrite orb_comm. simpl. reflexivity. 
       apply bop_and_elim in H. apply bop_and_elim in Q. 
          destruct H as [H1 H2]. destruct Q as [Q1 Q2].
          apply bop_or_elim in H1.  apply bop_or_elim in Q1. 
          destruct H1 as [H1 | H1]; destruct Q1 as [Q1 | Q1]. 
             rewrite H1. simpl. apply (IHs (a0 :: v) (a1 :: u) H2 Q2). 
             rewrite H1. simpl. apply (IHs (a0 :: v) (a1 :: u) H2 Q2). 
             rewrite List.app_comm_cons. rewrite (IHs (a0 :: v) (a1 :: u) H2 Q2). 
                rewrite (in_set_concat_intro S r u (a0 :: v) a (inl _ H1)). 
                rewrite orb_comm. simpl. reflexivity. 
             rewrite (in_set_concat_intro S r u (a0 :: v) a (inl _ H1)). 
                rewrite orb_comm. simpl. apply (IHs (a0 :: v) (a1 :: u) H2 Q2). 
Defined. 


Lemma bop_concat_set_commutative : bop_commutative (finite_set S) (brel_set r) (@bop_concat S).
Proof.  unfold bop_commutative, bop_concat.
        intros s t. unfold brel_set. unfold brel_and_sym. 
        apply bop_and_intro.
        apply subset_cat_left.        
        apply brel_subset_concat_right_intro. 
             right. apply brel_subset_reflexive; auto. 
             apply brel_subset_concat_right_intro. 
             left. apply brel_subset_reflexive; auto. 
          apply subset_cat_left.  apply brel_subset_concat_right_intro.
             right. apply brel_subset_reflexive; auto. 
             apply brel_subset_concat_right_intro. 
             left. apply brel_subset_reflexive; auto. 
Defined.

Lemma bop_concat_set_idempotent : bop_idempotent (finite_set S) (brel_set r) (@bop_concat S).
Proof.  unfold bop_idempotent, bop_concat.
        intro s. unfold brel_set. unfold brel_and_sym. 
        apply bop_and_intro. 
          apply subset_cat_left.  
                apply brel_subset_reflexive; auto. 
                apply brel_subset_reflexive; auto. 
          apply subset_cat_right.  
                apply brel_subset_reflexive; auto. 
                apply brel_subset_reflexive; auto. 
Defined. 


End Concat. 

Section DuplicateElim.
  Variable S: Type.
  Variable r : brel S.
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.

(* move duplicate elim lemmas ?*)

Lemma  uop_duplicate_elim_lemma_1 : 
   ∀ (a b: S),  r b a = true →     
       ∀ (X : finite_set S), in_set r (uop_duplicate_elim r (a :: X)) b = true.
Proof. intros a b E. induction X. 
          compute. rewrite E. reflexivity. 
          simpl. simpl in IHX. 
          case_eq(r a a0); case_eq(in_set r X a); case_eq(in_set r X a0); intros J K M; simpl.
          rewrite K in IHX. assumption. 
          rewrite (tranS _ _ _ E M). simpl. reflexivity. 
          apply symS in M.

          assert (A := in_set_right_congruence _ _ symS tranS _ _ _ M J). 
          rewrite A in K. discriminate. 
          rewrite (tranS _ _ _ E M). simpl. reflexivity.           
          rewrite K in IHX. assumption. 
          case_eq(r b a0); intro N. simpl. reflexivity. simpl. rewrite K in IHX. assumption. 
          rewrite E. simpl. reflexivity.           rewrite E. simpl. reflexivity. 
Defined.

Lemma uop_duplicate_elim_lemma_2 : 
   ∀ (a : S), 
     ∀ (X : finite_set S), 
       in_set r X a = false → 
           (uop_duplicate_elim r (a :: X)) = a :: (uop_duplicate_elim r X).
Proof. intros a X H. simpl. rewrite H. reflexivity. Defined. 


Lemma in_set_uop_duplicate_elim_intro : 
       ∀ (X : finite_set S) (a : S), 
         in_set r X a = true →
            in_set r (uop_duplicate_elim r X) a = true. 
Proof. induction X. 
          intros a I. compute in I. discriminate. 
          intros a0 I. 
          case_eq(in_set r X a); intro H. 
             unfold uop_duplicate_elim. rewrite H. apply IHX. 
             apply in_set_cons_elim in I. destruct I as [I | I].               
                apply (in_set_right_congruence _ _ symS tranS _ _ _ I H); auto. assumption. assumption. 

            apply in_set_cons_elim in I. destruct I as [I | I].
               apply uop_duplicate_elim_lemma_1; auto.  
               rewrite (uop_duplicate_elim_lemma_2 a X H). 
               unfold in_set. fold (@in_set S).
               case_eq(r a0 a); intro J. 
                  simpl. reflexivity.
                  simpl. apply IHX. assumption. assumption. 
Defined. 

Lemma in_set_uop_duplicate_elim_elim : 
       ∀ (X : finite_set S) (a : S), 
         in_set r (uop_duplicate_elim r X) a = true →
            in_set r X a = true.
Proof. induction X. 
          intros a I. compute in I. discriminate. 
          intros a0 I. unfold in_set. fold (@in_set S). 
          case_eq(r a0 a); intro H; simpl. 
             reflexivity.
             case_eq(in_set r X a); intro J. 
                 unfold uop_duplicate_elim in I. rewrite J in I. apply IHX. assumption. 
               rewrite (uop_duplicate_elim_lemma_2 a X J) in I. 
                 unfold in_set in I. fold (@in_set S) in I. rewrite H in I. simpl in I. 
                 assert (QED := IHX a0 I). assumption. 
Defined. 


Lemma in_set_dup_elim_intro : 
     ∀ (X : finite_set S) (t : S), in_set r X t = true → in_set r (uop_duplicate_elim r X) t = true. 
Proof. induction X; intros t H. 
       simpl in H. discriminate. 
       simpl. case_eq(in_set r X a); intro Q.
          unfold in_set in H.  fold (@in_set S) in H.  
          apply bop_or_elim in H. destruct H as [H | H].
          apply IHX. apply symS in H. apply (in_set_right_congruence S r symS tranS a t X H Q). 
          apply IHX. assumption. 
       unfold in_set. fold (@in_set S). 
          unfold in_set in H.  fold (@in_set S) in H.  
          apply bop_or_elim in H. destruct H as [H | H].
             rewrite H. simpl. reflexivity. 
             rewrite (IHX t H). rewrite orb_comm. simpl. reflexivity. 
Defined. 


Lemma uop_duplicate_elim_congruence_v1 : 
      uop_congruence_positive (finite_set S) (brel_subset r) (uop_duplicate_elim r).  
Proof. unfold uop_congruence_positive. 
       induction s; intros t H. 
          simpl. reflexivity. 
          unfold uop_duplicate_elim at 1. fold (@uop_duplicate_elim S r). 
          case_eq(in_set r s a); intro Q. 
             apply IHs. unfold brel_subset in H. fold (@brel_subset S) in H. 
                apply bop_and_elim in H.  destruct H as [H1 H2].  assumption. 
             unfold brel_subset in H. fold (@brel_subset S) in H. 
             unfold brel_subset. fold (@brel_subset S). 
             apply bop_and_elim in H.  destruct H as [H1 H2].
             apply bop_and_intro. 
                apply in_set_dup_elim_intro; auto. 
                apply IHs; auto. 
Defined. 

Lemma uop_duplicate_elim_congruence_v2 :
      uop_congruence_positive (finite_set S) (brel_set r) (uop_duplicate_elim r).  
Proof. unfold brel_set. unfold brel_and_sym. unfold uop_congruence_positive. intros s t H. 
       apply bop_and_elim in H. destruct H as [H1 H2]. 
       apply bop_and_intro. 
         apply uop_duplicate_elim_congruence_v1; auto. 
         apply uop_duplicate_elim_congruence_v1; auto. 
Defined.


Lemma uop_duplicate_elim_preserves_left_v1 : 
      uop_preserves_left_positive (finite_set S) (brel_subset r) (uop_duplicate_elim r).  
Proof. unfold uop_preserves_left_positive. 
       induction s; simpl; intros t H. 
          reflexivity. 
          apply bop_and_elim in H. destruct H as [H1 H2].
          case_eq(in_set r s a); intro Q. 
             apply IHs. assumption. 
             unfold brel_subset. fold (@brel_subset S). rewrite H1, (IHs t H2). simpl. reflexivity. 
Defined. 


Lemma uop_duplicate_elim_preserves_right_v1 : 
      uop_preserves_right_positive (finite_set S) (brel_subset r) (uop_duplicate_elim r).  
Proof. unfold uop_preserves_right_positive. 
       induction s; simpl; intros t H; auto. 
          apply bop_and_elim in H. destruct H as [H1 H2].
          rewrite (IHs t H2).  rewrite (in_set_dup_elim_intro t a H1); auto. 
Defined. 


Lemma uop_duplicate_elim_preserves_right_v2 : 
      uop_preserves_right_positive (finite_set S) (brel_set r) (uop_duplicate_elim r).  
Proof. intros w u. unfold brel_set. unfold brel_and_sym. intro H. 
       apply bop_and_elim in H. destruct H as [H1 H2]. 
       apply bop_and_intro. 
         apply uop_duplicate_elim_preserves_right_v1; auto. 
         apply uop_duplicate_elim_preserves_left_v1; auto. 
Defined. 

Lemma duplicate_elim_concat_associative : 
         uop_bop_associative (finite_set S) (brel_set r) (uop_duplicate_elim r) (@bop_concat S). 
Proof. unfold uop_bop_associative. intros s t v. 
       assert (H : brel_set r (bop_concat (bop_concat s t) v) 
                              (bop_concat (uop_duplicate_elim r (bop_concat s t)) v) = true).
          apply (bop_concat_set_congruence _ _ refS symS tranS
                 (bop_concat s t) v (uop_duplicate_elim r (bop_concat s t)) v). 
          apply uop_duplicate_elim_preserves_right_v2. 
          apply brel_set_reflexive; auto. 
          apply brel_set_reflexive; auto. 
       assert (K : brel_set r (bop_concat s (bop_concat t v)) 
                              (bop_concat s (uop_duplicate_elim r (bop_concat t v))) = true).
          apply (bop_concat_set_congruence _ _ refS symS tranS
                 s (bop_concat t v) s (uop_duplicate_elim r (bop_concat t v))). 
          apply brel_set_reflexive; auto. 
          apply uop_duplicate_elim_preserves_right_v2. 
          apply brel_set_reflexive; auto. 
          unfold bop_concat in *. rewrite List.app_assoc in K.           
          apply brel_set_symmetric in H. 
          apply (brel_set_transitive S r refS symS tranS _ _ _ H K). 
Defined. 


Lemma uop_duplicate_elim_preserves_left_v2 : 
      uop_preserves_left_positive (finite_set S) (@brel_set S r) (@uop_duplicate_elim S r).  
Proof. intros w u. unfold brel_set. unfold brel_and_sym. intro H. 
       apply bop_and_elim in H. destruct H as [H1 H2]. 
       apply bop_and_intro. 
         apply uop_duplicate_elim_preserves_left_v1; auto. 
         apply uop_duplicate_elim_preserves_right_v1; auto. 
Defined. 

End DuplicateElim. 



Section ThenUnary.
  Variable S: Type.
  Variable r : brel S.
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.

(* move then_unary lemmas ? *)

Lemma bop_then_unary_congruence : 
   ∀ (u : unary_op S) (b : binary_op S), 
           uop_congruence_positive S r u -> 
           bop_congruence S r b -> 
           bop_congruence S r (bop_then_unary u b).
Proof. intros u b congU congB. unfold bop_congruence, bop_then_unary.
       intros s1 s2 t1 t2 H Q. apply congU. apply congB.  assumption. assumption. 
Defined. 

Lemma bop_then_unary_associative : 
   ∀ (u : unary_op S) (b : binary_op S), 
           uop_congruence_positive S r u -> 
           uop_bop_associative S r u b -> 
           bop_associative S r (@bop_then_unary S u b).
Proof. intros u b congS assocS. unfold bop_associative, bop_then_unary.
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
   ∀ (u : unary_op S) (b : binary_op S), 
         uop_preserves_left_positive S r u -> 
         bop_idempotent S r b -> 
           bop_idempotent S r (@bop_then_unary S u b).
Proof. 
       intros u b presS idemS. 
       unfold bop_then_unary. unfold bop_idempotent. 
       intro s. apply (presS (b s s) s). apply idemS. 
Defined. 


Lemma bop_then_unary_commutative : 
   ∀ (u : unary_op S) (b : binary_op S), 
         uop_congruence_positive S r u -> 
         bop_commutative S r b -> 
           bop_commutative S r (@bop_then_unary S u b).
Proof. intros u b congS commS. 
       intros s t. unfold bop_then_unary. apply congS. apply commS. 
Defined. 

End ThenUnary. 

Section Union. 
  Variable S: Type.
  Variable r : brel S.
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.

Lemma in_set_bop_union_intro : ∀ (X Y : finite_set S) (a : S),
       (in_set r X a = true) + (in_set r Y a = true) → in_set r (bop_union r X Y) a = true. 
Proof. intros X Y a H. 
       unfold bop_union. unfold bop_then_unary. unfold bop_concat. 
       apply in_set_uop_duplicate_elim_intro; auto.
       apply in_set_concat_intro; auto. 
Defined. 

Lemma in_set_bop_union_elim : 
   ∀ (X Y : finite_set S) (a : S),
       in_set r (bop_union r X Y) a = true  →
       (in_set r X a = true) + (in_set r Y a = true). 
Proof. intros X Y a H. 
       unfold bop_union in H. unfold bop_then_unary in H. unfold bop_concat in H. 
       apply in_set_uop_duplicate_elim_elim in H. 
       apply in_set_concat_elim in H; auto.
Defined. 

  
Lemma bop_union_congruence : bop_congruence (finite_set S) (brel_set r) (bop_union r).
Proof. unfold bop_union.
       apply bop_then_unary_congruence. 
       apply uop_duplicate_elim_congruence_v2; auto. 
       apply bop_concat_set_congruence; auto. 
Defined. 

Lemma bop_union_associative : bop_associative (finite_set S) (brel_set r) (bop_union r).
Proof. unfold bop_union. 
       apply bop_then_unary_associative. 
       apply uop_duplicate_elim_congruence_v2; auto. 
       apply duplicate_elim_concat_associative; auto. 
Defined.

Lemma bop_union_idempotent : bop_idempotent (finite_set S) (brel_set r) (bop_union r).
Proof. unfold bop_union.
       apply bop_then_unary_idempotent.
       apply uop_duplicate_elim_preserves_left_v2; auto. 
       apply bop_concat_set_idempotent; auto. 
Defined. 

Lemma bop_union_commutative : bop_commutative(finite_set S) (brel_set r) (bop_union r).
Proof. unfold bop_union.
       apply bop_then_unary_commutative. 
       apply uop_duplicate_elim_congruence_v2; auto.  
       apply bop_concat_set_commutative; auto. 
Defined.


Lemma bop_union_not_selective : 
   ∀ (s : S) (f : S -> S), brel_not_trivial S r f -> bop_not_selective (finite_set S) (brel_set r) (bop_union r).
Proof. intros s f Pf.
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

Lemma bop_union_nil : ∀ (X : finite_set S), brel_set r (bop_union r nil X) X = true. 
Proof. intro X. 
       apply brel_set_intro. split. 
       apply brel_subset_intro; auto. 
       intros a H. apply in_set_bop_union_elim in H; auto. 
       destruct H as [H | H]. 
          unfold in_set in H. discriminate. 
          assumption. 
       apply brel_subset_intro; auto. 
       intros a H. apply in_set_bop_union_intro; auto. 
Defined. 


Lemma bop_union_nil_is_id : bop_is_id (finite_set S) (brel_set r) (bop_union r) nil.
Proof. intro s. 
       assert (fact1 : brel_set r (bop_union r nil s) s = true). 
          apply bop_union_nil; auto. 
       assert (fact2 : brel_set r (bop_union r s nil) (bop_union r nil s) = true). 
          apply bop_union_commutative; auto. 
       assert (fact3 : brel_set r (bop_union r s nil) s = true). 
          apply (brel_set_transitive S r refS symS tranS _ _ _ fact2 fact1). 
       rewrite fact1, fact3; auto. 
Defined. 
  
Lemma bop_union_exists_id : bop_exists_id (finite_set S) (brel_set r) (bop_union r).
Proof. exists nil. apply bop_union_nil_is_id; auto. Defined. 



Lemma bop_union_enum_is_ann (enum : carrier_is_finite S r) : 
  bop_is_ann (finite_set S) (brel_set r) (bop_union r) ((projT1 enum) tt).
Proof. destruct enum as [f Pf]. simpl.
       unfold bop_is_id. intro X. split.
       apply brel_set_intro_prop; auto.
       split.
       intros s H. apply in_set_bop_union_elim in H.
       destruct H as [H | H]; auto. 
       intros s H.  apply in_set_bop_union_intro.
       left; auto.

       apply brel_set_intro_prop; auto.
       split.
       intros s H. apply in_set_bop_union_elim in H.
       destruct H as [H | H]; auto. 
       intros s H.  apply in_set_bop_union_intro.
       right; auto.
Defined. 


Lemma bop_union_exists_ann (enum : carrier_is_finite S r) :
   bop_exists_ann (finite_set S) (brel_set r) (bop_union r).
Proof. exists ((projT1 enum) tt).
       apply (bop_union_enum_is_ann enum). 
Defined. 

Lemma bop_union_not_exists_ann (no_enum : carrier_is_not_finite S r) : 
   bop_not_exists_ann (finite_set S) (brel_set r) (bop_union r).
Proof.  unfold bop_not_exists_ann. intro X.
        unfold bop_not_is_ann. unfold carrier_is_not_finite in no_enum. 
        assert (K := no_enum (λ _, list_of_set S X)). simpl in K.
        destruct K as [s K].
        exists (s :: nil). 
        right. case_eq(brel_set r (bop_union r (s :: nil) X) X); intro J; auto.
        apply brel_set_elim_prop  in J; auto.        
        destruct J as [L R]. 
        assert (J := L s).
        assert (F : in_set r (bop_union r (s :: nil) X) s = true).
           apply in_set_bop_union_intro.              
           left. compute. rewrite refS; auto. 
        assert (M := J F).
        assert (N : in_list r (list_of_set S X) s = true). apply in_set_implies_in_list; auto.  
        rewrite N in K. discriminate K. 
Defined. 

Definition bop_union_exists_ann_decide (fin_d : carrier_is_finite_decidable S r) : bop_exists_ann_decidable (finite_set S) (brel_set r) (bop_union r)
 := match fin_d with
     | inl fS  => inl (bop_union_exists_ann fS) 
     | inr nfs => inr (bop_union_not_exists_ann nfs)
    end.


End Union.

End Theory.

Section ACAS.

Definition sg_CI_proofs_union : 
  ∀ (S : Type) (eqv : A_eqv S), sg_CI_proofs (finite_set S) (brel_set (A_eqv_eq S eqv)) (bop_union (A_eqv_eq S eqv))
  := λ S eqv,
let eqvP := A_eqv_proofs S eqv in
let symS := A_eqv_symmetric _ _ eqvP in
let refS := A_eqv_reflexive _ _ eqvP in
let trnS := A_eqv_transitive _ _ eqvP in     
let rS   := A_eqv_eq S eqv in
let s    := A_eqv_witness S eqv in
let f    := A_eqv_new S eqv in
let ntS  := A_eqv_not_trivial S eqv in       
let refS := A_eqv_reflexive S rS eqvP in
let symS := A_eqv_symmetric S rS eqvP in
let tranS := A_eqv_transitive S rS eqvP in                                                            
{|
  A_sg_CI_associative        := bop_union_associative S rS refS symS tranS 
; A_sg_CI_congruence         := bop_union_congruence S rS refS symS tranS 
; A_sg_CI_commutative        := bop_union_commutative S rS refS symS tranS 
; A_sg_CI_idempotent         := bop_union_idempotent S rS refS symS tranS 
; A_sg_CI_selective_d        := inr _ (bop_union_not_selective S rS refS symS s f ntS)
|}. 

Definition A_sg_CI_union : ∀ (S : Type),  A_eqv S -> A_sg_CI (finite_set S)
  := λ S eqv,
  let eqvP := A_eqv_proofs S eqv in
  let symS := A_eqv_symmetric _ _ eqvP in
  let refS := A_eqv_reflexive _ _ eqvP in
  let trnS := A_eqv_transitive _ _ eqvP in     
  let eqS  := A_eqv_eq S eqv in
  let s    := A_eqv_witness S eqv in
  let f    := A_eqv_new S eqv in
  let ntS  := A_eqv_not_trivial S eqv in       
   {| 
     A_sg_CI_eqv       := A_eqv_set S eqv
   ; A_sg_CI_bop       := bop_union eqS
   ; A_sg_CI_exists_id_d  := inl _ (bop_union_exists_id S eqS refS symS trnS)
   ; A_sg_CI_exists_ann_d := bop_union_exists_ann_decide S eqS refS symS trnS (A_eqv_finite_d S eqv)
   ; A_sg_CI_proofs    := sg_CI_proofs_union S eqv
   
   ; A_sg_CI_ast       := Ast_sg_union (A_eqv_ast S eqv)                                                                   
   |}. 
  

End ACAS.

Section CAS.

Definition  check_union_exists_ann {S : Type} (d : @check_is_finite S) : @check_exists_ann (finite_set S)
  := match d with
     | Certify_Is_Finite fS  => Certify_Exists_Ann (fS tt)
     | Certify_Is_Not_Finite => Certify_Not_Exists_Ann
     end.


Definition sg_CI_certs_union : ∀ {S : Type}, @eqv S -> @sg_CI_certificates (finite_set S)
:= λ {S} eqvS,  
let s   := eqv_witness eqvS in
let f   := eqv_new eqvS in
{|
  sg_CI_associative        := Assert_Associative  
; sg_CI_congruence         := Assert_Bop_Congruence  
; sg_CI_commutative        := Assert_Commutative  
; sg_CI_idempotent         := Assert_Idempotent  
; sg_CI_selective_d        := Certify_Not_Selective ((s :: nil), ((f s) :: nil))
|}. 



Definition sg_CI_union : ∀ {S : Type}, @eqv S -> @sg_CI (finite_set S)
:= λ {S} eqvS,
  let eqS := eqv_eq eqvS in
  let s   := eqv_witness eqvS in
  let f   := eqv_new eqvS in
   {| 
     sg_CI_eqv       := eqv_set eqvS
   ; sg_CI_bop       := bop_union eqS
   ; sg_CI_exists_id_d        := Certify_Exists_Id nil 
   ; sg_CI_exists_ann_d       := check_union_exists_ann (eqv_finite_d eqvS)
   ; sg_CI_certs     := sg_CI_certs_union eqvS
   
   ; sg_CI_ast       := Ast_sg_union(eqv_ast eqvS)
   |}. 


End CAS.

(*  union left order 

    X = X union Y <-> Y subset X 
*) 


Section Verify.


Lemma bop_union_certs_correct : 
    ∀ (S : Type) (eqvS : A_eqv S), 
      sg_CI_certs_union (A2C_eqv S eqvS)
      =                        
      P2C_sg_CI (finite_set S) (brel_set (A_eqv_eq S eqvS)) (bop_union (A_eqv_eq S eqvS))
                (sg_CI_proofs_union S eqvS).
Proof. intros S eqvS.
       destruct eqvS.
       unfold sg_CI_certs_union, sg_CI_proofs_union. unfold P2C_sg_CI. simpl.
       reflexivity.        
Qed. 
  

Theorem bop_union_correct (S : Type) (eqvS : A_eqv S) : 
         sg_CI_union (A2C_eqv S eqvS)  =  A2C_sg_CI (finite_set S) (A_sg_CI_union S eqvS). 
Proof. unfold sg_CI_union, A_sg_CI_union. unfold A2C_sg_CI. simpl.
       rewrite correct_eqv_set. 
       rewrite bop_union_certs_correct. 
       destruct eqvS. simpl.
       destruct A_eqv_finite_d as [[fS Pf] | NFS]; simpl; reflexivity.        
Qed.



End Verify.   
  
