Require Import Coq.Lists.List.
Require Import CAS.coq.common.compute.

Require Import CAS.coq.theory.set. (* for in_set lemmas *) 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.trivial. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.or.
Require Import CAS.coq.sg.and. 
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.product.

Require Import CAS.coq.uop.properties.

Import ListNotations.

Section Computation.

(*
• Phase 1. All pairs from X with equal active components are merged
into a single pair whose active component is the one found in the
original pairs and passive component is the join of passive components
from the original pairs. For instance, if X contains altogether three
pairs with a given x ∈ P , i.e., (x, x1 ), (x, x2 ) and (x, x3 ), then they are
replaced with a single pair (x, x1 ∨ x2 ∨ x3 ). Note that after phase 1
all pairs in X have distinct active components.

• Phase 2. All pairs from X that are dominated in X with respect
to their active components are deleted from X. For instance, if X
contains two pairs (x, x') and (y, y') such that x ≺ y, then the pair
(x, x') is deleted. In other words, phase 2 leaves in X only those pairs
that are efficient according to their active component.

TGG22: Note that Manger's order is the dual of our left order. 
*)   

(* 
  A = type of active component
  P = type of passive component
*)   
Fixpoint manger_merge_sets
           {A P : Type}
           (eqA : brel A)
           (addP : binary_op P)
           (Y : finite_set (A * P))
           (p1 : A * P) :=
  match Y with
  | nil => p1 :: nil
  | p2 :: Y' =>
    match p1, p2 with
    | (s1, t1), (s2, t2) =>
      if eqA s1 s2
      then manger_merge_sets eqA addP Y' (s1, addP t1 t2) 
      else p2 :: (manger_merge_sets eqA addP Y' p1) 
    end 
  end.



(* This makes the current proof that I am trying is bit easier.
The manger_merge_sets and manger_merge_sets_new can 
be proven equivalent, with some effort.
*)


Definition manger_merge_sets_new_aux
  {A P : Type}
  (eqA : brel A)
  (addP : binary_op P)
  (Y : finite_set (A * P))
  (p1 : A * P) : list (A * P) * list (A * P) :=
    ((filter (λ '(s2, t2), eqA (fst p1) s2) Y),
    (filter (λ '(s2, t2), negb (eqA (fst p1) s2)) Y)).


Definition manger_merge_sets_new
  {A P : Type}
  (eqA : brel A)
  (addP : binary_op P)
  (Y : finite_set (A * P))
  (p1 : A * P) : list (A * P) :=
    match manger_merge_sets_new_aux eqA addP Y p1 with 
    | (Y1, Y2) => 
        Y2 ++ 
        [(fold_left 
          (λ '(s1, t1) '(s2, t2), (s1, addP t1 t2)) 
          Y1 p1)] 
    end.

(* My claim is 

manger_merge_sets_new  = (* Notice the equality *)
manger_merge_sets

*)


Definition manger_phase_1_auxiliary 
          {A P : Type}
          (eqA : brel A)
          (addP : binary_op P) 
          (Y : finite_set (A * P))
          (X : finite_set (A * P))  : finite_set (A * P) :=
  fold_left (manger_merge_sets eqA addP) X Y.

Definition uop_manger_phase_1 
          {A P : Type}
          (eqA : brel A)
          (addP : binary_op P) 
          (X : finite_set (A * P))  : finite_set (A * P) :=
  manger_phase_1_auxiliary  eqA addP nil X.   

Definition equal_manger_phase_1 
          {A P : Type}
          (eqA : brel A)
          (eqP : brel P)          
          (addP : binary_op P) : brel (finite_set (A * P)) :=
  λ X Z, brel_set (brel_product eqA eqP)
                  (uop_manger_phase_1 eqA addP X)
                  (uop_manger_phase_1 eqA addP Z). 

Definition manger_pre_order
           {A P : Type}
           (lteA : brel A) : brel (A * P)
  := brel_product lteA (@brel_trivial P). 

Definition uop_manger_phase_2
           {A P : Type} (lteA : brel A) : unary_op (finite_set (A * P))          
  := uop_minset (manger_pre_order lteA). 

Definition equal_manger_phase_2
          {A P : Type}
          (eqA lteA : brel A)
          (eqP : brel P) : brel (finite_set (A * P)) :=         
  λ X Z, brel_set (brel_product eqA eqP)
                  (uop_manger_phase_2 lteA X)
                  (uop_manger_phase_2 lteA Z). 

Definition equal_manger
          {A P : Type}
          (eqA lteA : brel A)
          (eqP : brel P)          
          (addP : binary_op P) : brel (finite_set (A * P)) :=
  λ X Z, equal_manger_phase_1 eqA eqP addP 
                  (@uop_manger_phase_2 A P lteA X)
                  (@uop_manger_phase_2 A P lteA Z).

Definition equal_manger_v2
          {A P : Type}
          (eqA lteA : brel A)
          (eqP : brel P)          
          (addP : binary_op P) : brel (finite_set (A * P)) :=
  λ X Z, @equal_manger_phase_2 A P eqA lteA eqP 
                  (uop_manger_phase_1 eqA addP X)
                  (uop_manger_phase_1 eqA addP Z).

(* conjecture these two equalities are the same *) 

End Computation. 

Section Theory.

Variables (A P : Type) 
          (eqA lteA : brel A)
          (eqP : brel P)          
          (addP : binary_op P)
          (refA : brel_reflexive A eqA)
          (symA : brel_symmetric A eqA)
          (trnA : brel_transitive A eqA)
          (refP : brel_reflexive P eqP)
          (symP : brel_symmetric P eqP)
          (trnP : brel_transitive P eqP)
          (cong_addP : bop_congruence P eqP addP) 
          (cong_lteA : brel_congruence A eqA lteA)
          (ref_lteA : brel_reflexive A lteA)
          (* is idemP really needed, or is it 
             a consequence of using lists to represent sets?
          *) 
          (idemP : bop_idempotent P eqP addP). 


Local Notation "a [in] X" := (in_set (brel_product eqA eqP) X a = true) (at level 70).
Local Notation "a == b"   := (brel_product eqA eqP a b = true) (at level 70).
Local Notation "a <A> b"  := (eqA a b = false) (at level 70). 

Local Notation "[MMS]"  := (manger_merge_sets eqA addP).
Local Notation "[P1AX]" := (manger_phase_1_auxiliary eqA addP).
Local Notation "[P1]"   := (uop_manger_phase_1 eqA addP).
Local Notation "[P2]"   := (uop_manger_phase_2 lteA).

Local Notation "[EQ]"    := (brel_set (brel_product eqA eqP)).
Local Notation "a =S= b" := (brel_set (brel_product eqA eqP) a b = true) (at level 70). 
Local Notation "[EQ1]"   := (equal_manger_phase_1 eqA eqP addP). 
Local Notation "[EQM]"   := (equal_manger eqA lteA eqP addP).


(* equality on A * P *) 
Lemma refAP : brel_reflexive (A * P) (brel_product eqA eqP).
Proof. apply brel_product_reflexive; auto. Qed. 

Lemma symAP : brel_symmetric (A * P) (brel_product eqA eqP).
Proof. apply brel_product_symmetric; auto. Qed. 

Lemma trnAP : brel_transitive (A * P) (brel_product eqA eqP).
Proof. apply brel_product_transitive; auto. Qed. 

(* equality on set over A * P *)

Lemma refSetAP : brel_reflexive _ [EQ]. 
Proof. apply brel_set_reflexive.
       - apply refAP.
       - apply symAP. 
Qed. 

Lemma symSetAP : brel_symmetric _ [EQ]. 
Proof. apply brel_set_symmetric. Qed. 

Lemma trnSetAP : brel_transitive _ [EQ]. 
Proof. apply brel_set_transitive.
       - apply refAP.
       - apply symAP.
       - apply trnAP. 
Qed. 

Lemma set_equal_with_cons_left :
  ∀ X p1 p2, p1 == p2 -> (p1 :: X) =S= (p2 :: X) . 
Proof. intros X p1 p2 H1.
       apply brel_set_intro_prop.
       - apply refAP.
       - split; intros a H2. 
         + apply in_set_cons_intro; auto.
           * apply symAP.
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left. apply symAP in H1.
                   exact (trnAP _ _ _ H1 H2). 
                ++ right. exact H2. 
             -- apply symAP. 
         + apply in_set_cons_intro; auto.
           * apply symAP.
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left. 
                   exact (trnAP _ _ _ H1 H2). 
                ++ right. exact H2. 
             -- apply symAP. 
Qed.

Lemma set_equal_with_cons_right :
  ∀ X Y p, X =S= Y -> (p :: X) =S= (p :: Y) . 
Proof. intros X Y p H1.
       apply brel_set_intro_prop.
       - apply refAP.
       - split; intros a H2. 
         + apply in_set_cons_intro; auto.
           * apply symAP.
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left. exact H2.
                ++ right.
                   rewrite (in_set_left_congruence _ _ symAP trnAP a _ _ H1) in H2.
                   exact H2. 
            -- apply symAP. 
         + apply in_set_cons_intro; auto.
           * apply symAP.
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left. exact H2.
                ++ right.
                   rewrite (in_set_left_congruence _ _ symAP trnAP a _ _ H1).
                   exact H2. 
             -- apply symAP. 
Qed.

Lemma remove_duplicate_from_set :
  ∀ Y p1 p2, p1 == p2 -> (p1 :: p2 :: Y) =S= (p1 :: Y).
Proof. intros Y p1 p2 H1.
       apply brel_set_intro_prop.
       - apply refAP. 
       - split; intros a H2. 
         + apply in_set_cons_intro.
           * apply symAP. 
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left; auto. 
                ++ apply in_set_cons_elim in H2.
                   ** destruct H2 as [H2 | H2].
                      --- left. exact (trnAP _ _ _ H1 H2). 
                      --- right; auto. 
                   ** apply symAP. 
             -- apply symAP. 
         + apply in_set_cons_intro.
           * apply symAP. 
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left; auto. 
                ++ right.
                   apply in_set_cons_intro; auto.
                   apply symAP. 
             -- apply symAP.
Qed. 
                
Lemma set_rearrange_v1 :
  ∀ Y p1 p2, (p1 :: p2 :: Y) =S= (p2:: p1 :: Y).
Proof. intros Y p1 p2.
       apply brel_set_intro_prop.
       - apply refAP. 
       - split; intros p3 H1.
         + (*
  H1 : p3 [in] p1 :: p2 :: Y
  ============================
  p3 [in] p2 :: p1 :: Y
            *)
           apply in_set_cons_intro.
           * apply symAP.
           * apply in_set_cons_elim in H1.
             -- destruct H1 as [H1 | H1].
                ++ right.
                   apply in_set_cons_intro.
                   ** apply symAP.
                   ** left. auto. 
                ++ apply in_set_cons_elim in H1.
                   --- destruct H1 as [H1 | H1].
                       +++ left. auto.
                       +++ right. 
                           apply in_set_cons_intro.
                           *** apply symAP.
                           *** right. auto.
                   --- apply symAP.
             -- apply symAP.
         + (* same code! 

  H1 : p3 [in] p2 :: p1 :: Y
  ============================
  p3 [in] p1 :: p2 :: Y
           *)
           apply in_set_cons_intro.
           * apply symAP.
           * apply in_set_cons_elim in H1.
             -- destruct H1 as [H1 | H1].
                ++ right.
                   apply in_set_cons_intro.
                   ** apply symAP.
                   ** left. auto. 
                ++ apply in_set_cons_elim in H1.
                   --- destruct H1 as [H1 | H1].
                       +++ left. auto.
                       +++ right. 
                           apply in_set_cons_intro.
                           *** apply symAP.
                           *** right. auto.
                   --- apply symAP.
             -- apply symAP.
Qed.

Lemma set_rearrange_v2 : 
   ∀ X Y p,  p :: X ++ Y =S= X ++ p :: Y.
Proof. induction X; intros Y p. 
       - rewrite app_nil_l. rewrite app_nil_l.
         apply refSetAP. 
       - rewrite <- app_comm_cons. rewrite <- app_comm_cons. 
         assert (H1 := set_rearrange_v1 (X ++ Y) p a).
         assert (H2 := IHX Y p). 
         assert (H3 := set_equal_with_cons_right (p :: X ++ Y) (X ++ p :: Y) a H2). 
         exact (trnSetAP _ _ _ H1 H3).
Qed. 
                   
(* properties of manger_pre_order *)  

Lemma manger_pre_order_congruence : brel_congruence (A * P) (brel_product eqA eqP) (manger_pre_order lteA). 
Proof. unfold manger_pre_order.
       apply brel_product_congruence; auto.
       apply brel_trivial_congruence. 
Qed.

Lemma manger_pre_order_reflexive : brel_reflexive (A * P) (manger_pre_order lteA).
Proof. unfold manger_pre_order.
       apply brel_product_reflexive; auto.
       apply brel_trivial_reflexive. 
Qed.

(* properties of equality [EQ1] *)

Lemma equal_manger_phase_1_congruence : brel_congruence _ [EQ1] [EQ1].
Proof. intros X Y Z W. unfold equal_manger_phase_1.
       apply brel_set_congruence.
       - apply refAP. 
       - apply symAP. 
       - apply trnAP. 
Qed.

Lemma equal_manger_phase_1_reflexive : brel_reflexive _ [EQ1].
Proof. intro X. unfold equal_manger_phase_1. 
       apply brel_set_reflexive; auto. 
       + apply refAP. 
       + apply symAP. 
Qed. 

Lemma equal_manger_phase_1_symmetric : brel_symmetric _ [EQ1].
Proof. unfold equal_manger_phase_1. intros X Y. 
       apply brel_set_symmetric; auto.
Qed. 

Lemma equal_manger_phase_1_transitive : brel_transitive _ [EQ1].
Proof. unfold equal_manger_phase_1. intros X Y Z. 
       apply brel_set_transitive; auto.
       - apply refAP. 
       - apply symAP. 
       - apply trnAP. 
Qed. 

(* properties of equality [EQM] *)

Lemma equal_manger_congruence : brel_congruence _ [EQM] [EQM].
Proof. intros X Y Z W. unfold equal_manger. 
       apply equal_manger_phase_1_congruence.
Qed.

Lemma equal_manger_reflexive : brel_reflexive _ [EQM].
Proof. unfold equal_manger; intro X; 
       apply equal_manger_phase_1_reflexive.
Qed.        

Lemma equal_manger_symmetric : brel_symmetric _ [EQM].
Proof. unfold equal_manger; intros X Y; 
       apply equal_manger_phase_1_symmetric.
Qed.        


Lemma equal_manger_transitive : brel_transitive _ [EQM].
Proof. unfold equal_manger; intros X Y Z; 
       apply equal_manger_phase_1_transitive.
Qed.        

(* Idempotence of reductions *)

Definition fst_unique_in_set X :=
  ∀ a a' p p',  (a, p) [in] X ->  (a', p') [in] X -> ((a, p) == (a', p')) + (a <A> a').

Lemma singleton_uniqueness : ∀ p, fst_unique_in_set (p :: nil). 
Proof. destruct p as [a p].
       intros a1 a2 p1 p2 H2 H3. left.
       apply in_set_singleton_elim in H2, H3; try (apply symAP).
       apply symAP in H3.
       exact(trnAP _ _ _ H3 H2). 
Qed.

Lemma fst_unique_in_set_congruence :
  ∀ X Y, X =S= Y -> fst_unique_in_set X -> fst_unique_in_set Y.
Proof. unfold fst_unique_in_set.
       intros X Y H1 H2 a a' p p' H3 H4.
       assert (H5 : (a, p) [in] X).
       {
         rewrite (in_set_left_congruence _ _ symAP trnAP (a,p) _ _ H1).
         exact H3. 
       } 
       assert (H6 : (a', p') [in] X).
       {
         rewrite (in_set_left_congruence _ _ symAP trnAP (a',p') _ _ H1).
         exact H4. 
       } 
       exact (H2 _ _ _ _ H5 H6). 
Qed. 


Lemma fst_unique_in_set_cons_intro : 
  ∀ X a p, (∀ a' p',  (a', p') [in] X -> ((a, p) == (a', p')) + (a <A> a')) 
           -> (fst_unique_in_set X)
           -> fst_unique_in_set ((a,p) :: X). 
Proof. intros X a p H1 H2. unfold fst_unique_in_set.
       intros a' a'' p' p'' H3 H4.
       apply in_set_cons_elim in H3.
       - apply in_set_cons_elim in H4.
         + destruct H3 as [H3 | H3];
           destruct H4 as [H4 | H4].
           * left. apply symAP in H3.
             exact (trnAP _ _ _ H3 H4).
           * destruct (H1 _ _ H4) as [H5 | H5].
             -- left. apply symAP in H3.
                exact (trnAP _ _ _ H3 H5).
             -- right.
                apply brel_product_elim in H3.
                destruct H3 as [H3 _].
                case_eq(eqA a' a''); intro H6; auto.
                rewrite (trnA _ _ _ H3 H6) in H5.
                discriminate H5. 
           * destruct (H1 _ _ H3) as [H5 | H5].
             -- left. apply symAP in H5.
                exact (trnAP _ _ _ H5 H4).
             -- right.
                apply brel_product_elim in H4.
                destruct H4 as [H4 _].
                case_eq(eqA a' a''); intro H6; auto.
                apply symA in H6. rewrite (trnA _ _ _ H4 H6) in H5.
                discriminate H5. 
           * destruct (H1 _ _ H3) as [H5 | H5];
             destruct (H1 _ _ H4) as [H6 | H6].
             -- left. apply symAP in H5.
                exact (trnAP _ _ _ H5 H6).
             -- right.
                apply brel_product_elim in H5.
                destruct H5 as [H5 _].
                case_eq(eqA a' a''); intro H7; auto.
                rewrite (trnA _ _ _ H5 H7) in H6.
                discriminate H6.
             -- right.
                apply brel_product_elim in H6.
                destruct H6 as [H6 _].
                case_eq(eqA a' a''); intro H7; auto.
                apply symA in H7. rewrite (trnA _ _ _ H6 H7) in H5.
                discriminate H5.
             -- case_eq(eqA a' a''); intro H7.
                ++ left.
                   destruct (H2 _ _ _ _ H3 H4) as [H8 | H8].
                   ** exact H8. 
                   ** rewrite H7 in H8. discriminate H8.
                ++ right. reflexivity. 
         + apply symAP. 
       - apply symAP. 
Qed.

Lemma fst_unique_in_set_cons_elim : 
  ∀ X a p, fst_unique_in_set ((a,p) :: X) ->
           (∀ a' p',  (a', p') [in] X -> ((a, p) == (a', p')) + (a <A> a')) 
           * 
           (fst_unique_in_set X).
Proof. intros X a p H1. split. 
       - intros a' p' H2.
         unfold fst_unique_in_set in H1.
         assert (H3 : (a, p) [in] (a, p) :: X).
         {
           apply in_set_cons_intro; auto.
           + apply symAP.
           + left. apply refAP. 
         } 
         assert (H4 : (a', p') [in] (a, p) :: X). 
         {
           apply in_set_cons_intro; auto.
           + apply symAP.
         } 
         exact (H1 _ _ _ _ H3 H4). 
       - unfold fst_unique_in_set in *.
         intros a' a'' p' p'' H2 H3.
         assert (H4 : (a', p') [in] (a, p) :: X).
         {
           apply in_set_cons_intro; auto.
           + apply symAP.
         } 
         assert (H5 : (a'', p'') [in] (a, p) :: X).
         {
           apply in_set_cons_intro; auto.
           + apply symAP.
         } 
         exact (H1 _ _ _ _ H4 H5).          
Qed.

Lemma fst_unique_in_set_concat_elim_right :
  ∀ X Y, fst_unique_in_set (X ++ Y) -> fst_unique_in_set Y.
Proof. induction X; intros Y H1.
       - rewrite app_nil_l in H1. exact H1.
       - rewrite <- app_comm_cons in H1.
         destruct a as [a p]. 
         apply fst_unique_in_set_cons_elim in H1.
         destruct H1 as [_ H1].
         apply IHX; auto. 
Qed.                           

Lemma manger_merge_sets_unchanged : 
  ∀ Y a b p p',
    Y <> nil -> 
    a <A> b ->  (b, p') [in] ([MMS] Y (a, p)) -> (b, p') [in] Y. 
Proof. induction Y; intros s t p p' H0 H1 H2.
       - congruence. 
       - simpl in H2.
         destruct a as [a1 p1].
         case_eq(eqA s a1); intro H3; rewrite H3 in H2.
         + apply in_set_cons_intro.
           * apply symAP.
           * right. destruct Y.
             -- simpl in H2.
                apply bop_or_elim in H2.
                destruct H2 as [H2 | H2].
                ++ apply bop_and_elim in H2.
                   destruct H2 as [H2 H4].
                   apply symA in H2. rewrite H2 in H1.
                   discriminate H1.
                ++ discriminate H2. 
             -- assert (H4 : p0 :: Y ≠ nil). congruence.
                exact(IHY _ _ _ _ H4 H1 H2). 
         + apply in_set_cons_intro. 
           * apply symAP. 
           * destruct Y.
             -- simpl in H2.
                apply bop_or_elim in H2.
                destruct H2 as [H2 | H2].
                ** left. apply bop_and_elim in H2.
                   destruct H2 as [H2 H4]. 
                   apply brel_product_intro; auto. 
                ** apply bop_or_elim in H2.
                   destruct H2 as [H2 | H2].
                   --- apply bop_and_elim in H2.
                       destruct H2 as [H2 H4].
                       apply symA in H2. rewrite H2 in H1.
                       discriminate H1.
                   --- discriminate H2. 
             -- apply in_set_cons_elim in H2.
                ++ destruct H2 as [H2 | H2].
                   ** left. exact H2.
                   ** right.
                      assert (H4 : p0 :: Y ≠ nil). congruence. 
                      exact (IHY _ _ _ _ H4 H1 H2).
                ++ apply symAP. 
Qed. 



Lemma manger_merge_sets_unchanged_v2 : 
  ∀ Y a b p p',
    Y <> nil -> 
    a <A> b -> (b, p') [in] Y -> (b, p') [in] ([MMS] Y (a, p)).
Proof. induction Y; intros a1 a2 p1 p2 H0 H1 H2.
       - congruence. 
       - destruct a as [a3 p3].
         simpl. 
         apply in_set_cons_elim in H2.
         + destruct H2 as [H2 | H2]; 
             case_eq(eqA a1 a3); intro H3.
           * apply brel_product_elim in H2.
             destruct H2 as [H2 H4].
             rewrite (trnA _ _ _ H3 H2) in H1.
             discriminate H1. 
           * apply in_set_cons_intro.
             -- apply symAP.
             -- left. exact H2. 
           * destruct Y. 
             -- compute in H2. discriminate H2.
             -- assert (H4 : p :: Y ≠ nil). congruence.  
                exact(IHY _ _ (addP p1 p3) _ H4 H1 H2).
           * destruct Y. 
             -- compute in H2. discriminate H2.
             -- assert (H4 : p :: Y ≠ nil). congruence.  
                assert (H5 := IHY _ _ p1 _ H4 H1 H2).
                apply in_set_cons_intro.
                ++ apply symAP.
                ++ right. auto. 
         + apply symAP. 
Qed. 

Lemma manger_merge_sets_preserves_uniqueness : 
∀ Y p, fst_unique_in_set Y -> fst_unique_in_set ([MMS] Y p). 
Proof. induction Y; intros p H1. 
       - simpl. apply singleton_uniqueness.
       - destruct a as [a1 p1]. destruct p as [a2 p2].
         apply fst_unique_in_set_cons_elim in H1.
         destruct H1 as [H1 H2]. simpl.
         case_eq(eqA a2 a1); intro H3.
         + apply IHY. exact H2. 
         + apply fst_unique_in_set_cons_intro.
           * intros a' p' H4.
             case_eq(eqA a1 a'); intro H5.
             -- left. apply brel_product_intro; auto.
                assert (H6' : (a', p') == (a1, p')).
                {
                  apply brel_product_intro; auto. 
                } 
                assert (H6 : (a1, p') [in] [MMS] Y (a2, p2)).
                {
                  exact (in_set_right_congruence _ _ symAP trnAP _ _ _ H6' H4).
                }
                destruct Y.
                ++ simpl in H6. apply bop_or_elim in H6.
                   destruct H6 as [H6 | H6]. 
                   ** apply bop_and_elim in H6.
                      destruct H6 as [H6 H7].
                      apply symA in H6. rewrite H6 in H3.
                      discriminate H3.
                   **  discriminate H6.
                ++ assert (H99 : p :: Y <> nil). congruence. 
                   assert (H6'' := manger_merge_sets_unchanged _ _ _ _ _ H99 H3 H6). 
                   destruct (H1 _ _ H6'') as [H7 | H7].
                   ** apply brel_product_elim in H7; auto.
                      destruct H7 as [_ H7]. exact H7. 
                   ** rewrite refA in H7. discriminate H7.
             -- right. reflexivity. 
           * apply IHY; auto.
Qed. 


Lemma uop_manger_phase_1_auxiliary_preserves_uniqueness : 
    ∀ X Y, fst_unique_in_set Y -> fst_unique_in_set ([P1AX] Y X). 
Proof. induction X; intros Y H1.
       - simpl. exact H1. 
       - simpl. apply IHX.
         apply manger_merge_sets_preserves_uniqueness; auto. 
Qed. 

Lemma manger_merge_set_congruence_right :
  ∀ Y p1 p2, p1 == p2 -> ([MMS] Y p1) =S= ([MMS] Y p2). 
Proof. induction Y; intros [a1 p1] [a2 p2] H1.
       - simpl.
         apply set_equal_with_cons_left; auto. 
       - apply brel_product_elim in H1. 
         destruct H1 as [H1 H2]. 
         destruct a as [a3 p3]. simpl.
         case_eq(eqA a1 a3); intro H3; case_eq(eqA a2 a3); intro H4.
         + assert (H5 : (a1, addP p1 p3) == (a2, addP p2 p3)).
           {
             apply brel_product_intro; auto.
           }
           exact (IHY _ _ H5). 
         + apply symA in H1.
           rewrite (trnA _ _ _ H1 H3) in H4.
           discriminate H4. 
         + rewrite (trnA _ _ _ H1 H4) in H3.
           discriminate H3. 
         + assert (H5 : (a1, p1) == (a2, p2)).
           {
             apply brel_product_intro; auto.
           }
           assert (H6 := IHY _ _ H5).
           exact (set_equal_with_cons_right _ _ (a3, p3) H6). 
Qed.




Lemma filter_negb : 
  forall (X : list (A * P))
  (f : A -> bool),
  List.filter (λ '(s2, _), negb (f s2)) X ++ 
  List.filter (λ '(s2, _), f s2) X =S= X.
Proof.
  induction X as [|(ax, bx) X Ihx];
  intros f; cbn.
  + reflexivity.
  + case_eq (f ax); intros Ha;
    simpl.
    ++
      remember (List.filter (λ '(s2, _), 
        negb (f s2)) X) as Xt.
      remember (List.filter (λ '(s2, _), 
        f s2) X) as Yt.
      apply symSetAP.
      eapply trnSetAP.
      instantiate (1 := (ax, bx) :: Xt ++ Yt).
      +++
        apply set_equal_with_cons_right,
        symSetAP; subst; apply Ihx.
      +++
        apply set_rearrange_v2.
    ++
      apply set_equal_with_cons_right,
      Ihx.
Qed.



Lemma filter_congruence_gen : 
  forall X Y f,
  (theory.bProp_congruence _ 
    (brel_product eqA eqP) f) ->
  X =S= Y ->
  filter f X =S=
  filter f Y.
Proof.
  intros ? ? ? Fcong Ha.
  apply brel_set_intro_prop.
  + apply refAP.
  + split.
    ++
      intros (a, p) Hb.
      eapply in_set_filter_elim in Hb.
      destruct Hb as [Hbl Hbr].
      eapply in_set_filter_intro;
      [apply symAP | apply Fcong | 
        split; [exact Hbl | ]].
      apply brel_set_elim_prop in Ha.
      destruct Ha as [Hal Har].
      apply Hal, Hbr.
      apply symAP.
      apply trnAP.
      apply Fcong.
    ++ 
      intros (a, p) Hb.
      eapply in_set_filter_elim in Hb.
      destruct Hb as [Hbl Hbr].
      eapply in_set_filter_intro;
      [apply symAP | apply Fcong | 
        split; [exact Hbl | ]].
      apply brel_set_elim_prop in Ha.
      destruct Ha as [Hal Har].
      apply Har, Hbr.
      apply symAP.
      apply trnAP.
      apply Fcong.
  Qed. 



Lemma manger_merge_set_new_aux_congruence_left :
  ∀ X Y pa, 
  X =S= Y -> 
  (filter (λ '(s2, _), negb (eqA pa s2)) X =S= 
    filter (λ '(s2, _), negb (eqA pa s2)) Y) ∧
  (filter (λ '(s2, _), eqA pa s2) X =S= 
    filter (λ '(s2, _), eqA pa s2) Y).
Proof.
  intros ? ? ? Ha.
  pose proof (filter_negb X (fun x => negb (eqA pa x))) as Hb.
  pose proof (filter_negb Y (eqA pa)) as Hc.
  apply symSetAP in Hc.
  pose proof (trnSetAP _ _ _ Ha Hc) as Hd.
  split.
  + assert (He : theory.bProp_congruence _ 
      (brel_product eqA eqP)
      (λ '(s2, _), negb (eqA pa s2))).
    unfold theory.bProp_congruence.
    intros (aa, ap) (ba, bp) He.
    f_equal.
    apply brel_product_elim in He.
    destruct He as [Hel Her].
    case_eq (eqA pa aa); intro Hf.
    rewrite (trnA pa aa ba Hf Hel);
    reflexivity.
    case_eq (eqA pa ba); intro Hg.
    apply symA in Hel.
    rewrite (trnA pa ba aa Hg Hel) in Hf;
    congruence.
    reflexivity.
    eapply filter_congruence_gen;
    [exact He | exact Ha].
  + assert (He : theory.bProp_congruence _ 
      (brel_product eqA eqP)
      (λ '(s2, _), eqA pa s2)).
    unfold theory.bProp_congruence.
    intros (aa, ap) (ba, bp) He.
    apply brel_product_elim in He.
    destruct He as [Hel Her].
    case_eq (eqA pa aa); intro Hf.
    rewrite (trnA pa aa ba Hf Hel);
    reflexivity.
    case_eq (eqA pa ba); intro Hg.
    apply symA in Hel.
    rewrite (trnA pa ba aa Hg Hel) in Hf;
    congruence.
    reflexivity.
    eapply filter_congruence_gen;
    [exact He | exact Ha].
Qed.
  

(* 
Another challenge and it probably need 
idempotence on addP

[(1, 2); (1, 3); (1, 2)] =S= 
[(1, 2); (1, 3)]

To make the life easier, I can turn 
the first list 
[(1, 2); (1, 3); (1, 2)] =S= 
[(1, 2); (1, 2); (1, 3)]

Now when I reduce, the first two will be
[(1, 2); (1, 3)] -> 
[(1, 2 + 3)]

*)

Lemma fold_left_congruence : 
  forall (X Y : list (A * P)) 
  (pa : A) (pb : P),
  (forall u v, (u, v) [in] X -> eqA u pa = true) ->
  (forall u v, (u, v) [in] Y -> eqA u pa = true) ->
  X =S= Y ->
  [fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2)) 
    X (pa, pb)] =S= 
  [fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2)) 
    Y (pa, pb)].
Proof.
Admitted.  


(* generalise this one *)
Lemma manger_merge_set_new_aux_fold_filter :
  ∀ (X Y : list (A * P)) (pa : A) (pb : P), 
  X =S= Y -> 
  [fold_left (λ '(s1, t1) '(_, t2), 
    (s1, addP t1 t2)) 
    (filter (λ '(s2, _), eqA pa s2) X) 
    (pa, pb)] =S= 
  [fold_left (λ '(s1, t1) '(_, t2), 
    (s1, addP t1 t2))
    (filter (λ '(s2, _), eqA pa s2) Y) 
    (pa, pb)].
Proof.
  intros ? ? ? ? Ha.
  assert (Hb : theory.bProp_congruence _  
    (brel_product eqA eqP)
    (λ '(s2, _), eqA pa s2)).
  intros (aa, ap) (ba, bp) He.
  apply brel_product_elim in He.
  destruct He as [Hel Her].
  case_eq (eqA pa aa); intro Hf.
  rewrite (trnA pa aa ba Hf Hel);
  reflexivity.
  case_eq (eqA pa ba); intro Hg.
  apply symA in Hel.
  rewrite (trnA pa ba aa Hg Hel) in Hf;
  congruence.
  reflexivity.
  pose proof filter_congruence_gen 
    X Y (λ '(s2, _), eqA pa s2) Hb Ha as Hc.
  remember (filter (λ '(s2, _), eqA pa s2) X) 
  as Xf.
  remember (filter (λ '(s2, _), eqA pa s2) Y) 
  as Yf.
  eapply fold_left_congruence.
  + intros ? ? Hd.
    rewrite HeqXf in Hd.
    eapply in_set_filter_elim in Hd;
    firstorder.
  + intros ? ? Hd.
    rewrite HeqYf in Hd.
    eapply in_set_filter_elim in Hd;
    firstorder.
  + exact Hc.
Qed. 


  


Lemma append_congruence : 
  forall X₁ X₂ Y₁ Y₂ : list (A * P), 
  X₁ =S= Y₁ -> 
  X₂ =S= Y₂ ->
  X₁ ++ X₂ =S= Y₁ ++ Y₂.
Proof.
  intros ? ? ? ? Ha Hb.
  apply brel_set_elim_prop in Ha, Hb;
  try (repeat apply symAP; repeat apply trnAP).
  destruct Ha as [Hal Har].
  destruct Hb as [Hbl Hbr].
  apply brel_set_intro_prop.
  apply refAP.
  split.
  + intros (a, b) Hc.
    apply in_set_concat_elim in Hc.
    destruct Hc as [Hc | Hc].
    apply in_set_concat_intro.
    left.
    apply Hal; exact Hc.
    apply in_set_concat_intro.
    right.
    apply Hbl; exact Hc.
    apply symAP.
  + intros (a, b) Hc.
    apply in_set_concat_elim in Hc.
    destruct Hc as [Hc | Hc].
    apply in_set_concat_intro.
    left.
    apply Har; exact Hc.
    apply in_set_concat_intro.
    right.
    apply Hbr; exact Hc.
    apply symAP.
Qed.

Local Notation "[MMSN]"  := 
  (manger_merge_sets_new eqA addP).

Lemma manger_merge_set_new_congruence_left :
  ∀ X Y p, 
  X =S= Y -> [MMSN] X p =S= [MMSN] Y p.
Proof.
  unfold manger_merge_sets_new,
  manger_merge_sets_new_aux.
  intros ? ? (pa, pb) Ha; cbn.
  pose proof 
    (manger_merge_set_new_aux_congruence_left X Y pa Ha) as 
    [Hb Hc].
  eapply append_congruence;
  [exact Hb | 
    eapply manger_merge_set_new_aux_fold_filter;
    exact Ha].
Qed.



Lemma manger_merge_set_congruence_left :
  ∀ Y Y' p, Y =S= Y' -> ([MMS] Y p) =S= ([MMS] Y' p).
Proof.
Admitted.

Lemma uop_manger_phase1_auxiliary_congurence_left :
  ∀ X Y1 Y2,  Y1 =S= Y2 -> [P1AX] Y1 X =S= [P1AX] Y2 X. 
Proof. induction X; intros Y1 Y2 H1; simpl. 
       - exact H1. 
       - assert (H2 := manger_merge_set_congruence_left _ _ a H1). 
         apply IHX; auto.
Qed.

Lemma  fst_unique_in_set_implies_manger_merge_set_fixpoint : 
∀ Y a' p', fst_unique_in_set ((a', p') :: Y) -> ([MMS] Y (a',p')) =S= ((a', p') :: Y). 
Proof. induction Y; intros a' p' H1; simpl. 
       - apply refSetAP. 
       - destruct a as [a p].
         case_eq(eqA a' a); intro H2.
         + case_eq(eqP p' p); intro H7.
           * assert (H3 : ((a', p') :: (a, p) :: Y) =S= ((a', p') :: Y)).
             {
               assert (H4 : (a', p') == (a, p)).
               {
                 apply brel_product_intro; auto. 
               } 
               exact (remove_duplicate_from_set Y _ _ H4). 
             } 
             assert (H4 : fst_unique_in_set ((a', p') :: Y)).
             {
               exact (fst_unique_in_set_congruence _ _ H3 H1). 
             } 
             assert (H5 := IHY _ _ H4).
             apply symSetAP in H3.
             assert (H6 := trnSetAP _ _ _ H5 H3).
             assert (H8 := cong_addP _ _ _ _(refP p') H7).
             assert (H9 := idemP p'). apply symP in H9.
             assert (H10 := trnP _ _ _ H9 H8).
             assert (H11 : (a', addP p' p) == (a', p')).
             {
               apply brel_product_intro; auto. 
             }
             assert (H12 : [MMS] Y (a', addP p' p) =S= [MMS] Y (a', p')).
             {
               exact(manger_merge_set_congruence_right Y _ _ H11). 
             } 
             exact(trnSetAP _ _ _ H12 H6). 
           * apply fst_unique_in_set_cons_elim in H1.
             destruct H1 as [H1 H3]. 
             apply fst_unique_in_set_cons_elim in H3.
             destruct H3 as [H3 H4].
             assert (H5 : (a, p) [in] (a, p) :: Y).
             {
               apply in_set_cons_intro.
               -- apply symAP.
               -- left. apply brel_product_intro.
                  apply refA. apply refP. 
             } 
             assert (H6 := H1 _ _ H5).
             destruct H6 as [H6 | H6].
             -- apply brel_product_elim in H6.
                destruct H6 as [_ H6].
                rewrite H6 in H7. discriminate H7. 
             -- rewrite H6 in H2. discriminate H2. 
         + assert (H3 : (a, p) :: (a', p') :: Y =S= (a', p') :: (a, p) :: Y).
           {
             apply set_rearrange_v1. 
           } 
           assert (H4 : fst_unique_in_set ((a', p') :: Y)).
           {
             apply symSetAP in H3. 
             assert (H5 := fst_unique_in_set_congruence _ _ H3 H1).
             apply fst_unique_in_set_cons_elim in H5.
             destruct H5 as [_ H5].
             exact H5. 
           } 
           assert (H5 := IHY _ _ H4).
           assert (H6 : (a, p) :: ([MMS] Y (a', p')) =S= (a, p) :: (a', p') :: Y).
           {
             exact (set_equal_with_cons_right _ _ (a, p) H5). 
           } 
           exact (trnSetAP _ _ _ H6 H3). 
Qed. 
         
Lemma  fst_unique_in_set_implies_uop_manger_phase_1_auxiliary_fixpoint_general : 
∀ X Y, fst_unique_in_set (X ++ Y) -> ([P1AX] Y X) =S= (X ++ Y). 
Proof. induction X; intros Y H1.
       - simpl.
         apply brel_set_reflexive; auto.
         + apply refAP. 
         + apply symAP.          
       - destruct a as [a p].
         rewrite <- app_comm_cons in H1.
         rewrite <- app_comm_cons. simpl.
         assert (H4 : (a, p) :: X ++ Y =S= X ++ (a, p) :: Y). 
         {
           apply set_rearrange_v2. 
         } 
         assert (H2: fst_unique_in_set (X ++ ((a, p) :: Y))).
         {
           exact (fst_unique_in_set_congruence _ _ H4 H1). 
         } 
         assert (H3 := IHX _ H2).
         assert (H3' : fst_unique_in_set ((a, p) :: Y)).
         {
           exact (fst_unique_in_set_concat_elim_right _ _ H2). 
         } 
         assert (H4' : ([MMS] Y (a, p)) =S= ((a, p) :: Y)).
         {
           exact (fst_unique_in_set_implies_manger_merge_set_fixpoint _ _ _ H3'). 
         } 
         assert (H5 : [P1AX] ([MMS] Y (a, p)) X =S= [P1AX] ((a, p) :: Y) X).
         {
           exact (uop_manger_phase1_auxiliary_congurence_left _ _ _ H4'). 
         }
         apply symSetAP in H4. 
         exact (trnSetAP _ _ _ (trnSetAP _ _ _ H5 H3) H4). 
Qed. 

             
Lemma  fst_unique_in_set_implies_uop_manger_phase_1_auxiliary_fixpoint : 
∀ X, fst_unique_in_set X -> ([P1AX] nil X) =S= X. 
Proof. intro X.
       assert (H1 := fst_unique_in_set_implies_uop_manger_phase_1_auxiliary_fixpoint_general X nil).
       rewrite app_nil_r in H1.
       exact H1. 
Qed. 

Lemma uop_manger_phase_1_auxiliary_uop_idempotent :
  ∀ X Y,  fst_unique_in_set Y -> [P1AX] nil ([P1AX] Y X) =S= [P1AX] Y X. 
Proof. intros X Y H1.
       assert (H2 := uop_manger_phase_1_auxiliary_preserves_uniqueness X Y H1).
       apply fst_unique_in_set_implies_uop_manger_phase_1_auxiliary_fixpoint; auto. 
Qed. 

Lemma fst_unique_in_empty_set : fst_unique_in_set nil.
Proof. intros a a' p p' H. compute in H. discriminate H. Qed.

Lemma uop_manger_phase_1_uop_idempotent : uop_idempotent _ [EQ] [P1]. 
Proof. intro X. unfold uop_manger_phase_1.
       apply uop_manger_phase_1_auxiliary_uop_idempotent.
       apply fst_unique_in_empty_set. 
Qed. 

Lemma uop_manger_phase_2_uop_idempotent : uop_idempotent _ [EQ] [P2]. 
Proof. intro X. unfold uop_manger_phase_2.  
       apply uop_minset_idempotent.
       - apply refAP. 
       - apply symAP. 
       - apply trnAP. 
       - apply manger_pre_order_congruence. 
       - apply manger_pre_order_reflexive.
Qed.          

End Theory.   
