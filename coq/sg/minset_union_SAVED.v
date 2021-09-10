
Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset.
Require Import CAS.coq.theory.reduction.classical.
Require Import CAS.coq.theory.reduction.full.  
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.
Require Import CAS.coq.sg.union.

Section Theory.

Variable S  : Type. 
Variable rS : brel S.

Variable wS : S.
Variable f : S -> S.                
Variable Pf : brel_not_trivial S rS f. 

Variable congS : brel_congruence S rS rS. 
Variable refS  : brel_reflexive S rS.
Variable symS  : brel_symmetric S rS.  
Variable tranS : brel_transitive S rS.

Variable lteS : brel S.
Variable lteCong : brel_congruence S rS lteS.
Variable lteRefl : brel_reflexive S lteS.
Variable lteTrans : brel_transitive S lteS. 
Variable lteAntiSym : brel_antisymmetric S rS lteS.


Definition bop_minset_union : binary_op (finite_set S)
  := bop_full_reduce (uop_minset rS lteS) (bop_union rS).

Definition MS   := uop_minset rS lteS.
Definition EQMS := brel_minset rS lteS.
Definition EQS  := brel_set rS.
Definition U    := bop_union rS.
Definition MSU  := bop_minset_union. 

Notation "a [=] b"    := (rS a b = true)          (at level 15).
Notation "a [<>] b"   := (rS a b = false)         (at level 15).
Notation "a [=S] b"   := (EQS a b = true)         (at level 15).
Notation "a [<>S] b"  := (EQS a b = false)        (at level 15).
Notation "a [=MS] b"  := (EQMS a b = true)        (at level 15).
Notation "a [<>MS] b" := (EQMS a b = false)       (at level 15).

Notation "a [in] b"  := (in_set rS b a = true)   (at level 15).
Notation "a [!in] b" := (in_set rS b a = false)  (at level 15).
Notation "a [<=] b"  := (lteS a b = true)        (at level 15).
Notation "a [!<=] b" := (lteS a b = false)       (at level 15).


Definition set_transitive := brel_set_transitive S rS refS symS tranS.
Definition set_symmetric := brel_set_symmetric S rS.
Definition set_reflexive := brel_set_reflexive S rS refS symS.
Definition minset_idempotent := uop_minset_idempotent S rS congS refS symS tranS lteS lteCong lteRefl. 
Definition minset_transitive := brel_minset_transitive S rS refS symS tranS lteS.
Definition minset_symmetric := brel_minset_symmetric S rS lteS.
Definition minset_reflexive := brel_minset_reflexive S rS refS symS lteS. 
Definition minset_congruence := uop_minset_congruence S rS congS refS symS tranS lteS lteCong.

Lemma bop_minset_union_congruence : bop_congruence (finite_set S) EQMS bop_minset_union.
Proof. apply bop_full_reduce_congruence. 
       apply (uop_minset_congruence _ _ congS refS symS tranS lteS lteCong). 
       apply bop_union_congruence; auto. 
Qed.

Lemma in_set_bop_reduce_union_elim (a : S) (X Y : finite_set S) :
  a [in] (bop_reduce MS U X Y) -> ((a [in] X) + (a [in] Y)) * (∀ (s : S), ((s [in] X) + (s [in] Y)) -> (s [!<=] a) + (s [=] a)).
Proof. intro H. 
       unfold bop_reduce in H.
       apply in_set_minset_elim in H; auto. destruct H as [L R]. 
       apply in_set_bop_union_elim in L; auto.
       split. destruct L as [ L | L ]; auto.       
       intros s [inX | inY].
       assert (J : in_set rS (bop_union rS X Y) s = true). apply in_set_bop_union_intro; auto. 
       destruct (R s J) as [E | NLTE ]; auto. 
       assert (J : in_set rS (bop_union rS X Y) s = true). apply in_set_bop_union_intro; auto. 
       destruct (R s J) as [E | NLTE ]; auto.
Qed.               

Lemma in_set_bop_reduce_union_intro (a : S) (X Y : finite_set S) :
  ((a [in] X) + (a [in] Y)) * (∀ (s : S), ((s [in] X) + (s [in] Y)) -> (s [!<=] a) + (s [=] a)) -> a [in] (bop_reduce MS U X Y). 
Proof. intros [ inX_or_inY  H ]. 
       unfold bop_reduce. 
       apply in_set_minset_intro; auto. 
       split. apply in_set_bop_union_intro; auto. 
       intros s J. apply in_set_bop_union_elim in J; auto.
       assert (K := H s J). destruct K; auto. 
Qed.


Lemma bop_left_uop_minset_invariant : bop_left_uop_invariant (finite_set S) EQS (bop_reduce MS U) MS. 
Proof. unfold bop_left_uop_invariant. intros X Y.
       apply brel_set_intro_prop; auto. split.

       intros a H. 
       apply in_set_bop_reduce_union_intro. apply in_set_bop_reduce_union_elim in H. destruct H as [ H1 H2 ].    
       destruct H1 as [L | R].
          (* L : a [in] MS X *) 
          split. 
             left. apply in_set_minset_elim in L; auto. destruct L as [L _]. exact L. 
             intros s [s_in_X | s_in_Y].
                (* s in X *)
                case_eq(in_set rS (uop_minset rS lteS X) s); intro J. 
                   apply H2; auto. 
                   destruct (in_set_uop_minset_false_elim S rS wS f Pf congS refS symS tranS lteS lteCong lteRefl lteTrans s X s_in_X J)
                            as [s' [[H3 H4] H5]]. 
                   destruct (H2 s' (inl H3)) as [H6 | H6].
                      left. case_eq(lteS s a); intro H7; auto. 
                      rewrite (lteTrans _ _ _ H4 H7) in H6. exact H6.
                      rewrite (lteCong _ _ _ _ H6 (refS s)) in H4. 
                      left. case_eq(lteS s a); intro H7; auto.
(* I don't think we really need antisym...
                     
                      assert (F : s [in] uop_minset rS lteS X).
                         apply in_set_minset_intro; auto.
                         split; auto.
                         apply in_set_minset_elim in L; auto.
                         destruct L as [L1 L2].
                         intros t H8.
                         assert (G := L2 t H8). 
                         destruct G as [G | G].
                            right.
                            case_eq(lteS t s); intro I; auto. 
*)                          
                      assert (H8 := lteAntiSym _ _ H4 H7).
                      assert (H9 := tranS _ _ _ H6 H8).
                      rewrite H9 in H5. exact H5.
                (* s in Y *)
                apply H2; auto. 
          (* R : a [in] Y *)
          split.                 
             right. exact R. 
             intros s [s_in_X | s_in_Y].
                (* s in X *)
                case_eq(in_set rS (uop_minset rS lteS X) s); intro J. 
                   apply H2; auto. 
                   destruct (in_set_uop_minset_false_elim S rS wS f Pf congS refS symS tranS lteS lteCong lteRefl lteTrans s X s_in_X J)
                            as [s' [[H3 H4] H5]]. 
                   destruct (H2 s' (inl H3)) as [H6 | H6].
                      left. case_eq(lteS s a); intro H7; auto. 
                      rewrite (lteTrans _ _ _ H4 H7) in H6. exact H6.
                      rewrite (lteCong _ _ _ _ H6 (refS s)) in H4. 
                      left. case_eq(lteS s a); intro H7; auto.
                      assert (H8 := lteAntiSym _ _ H4 H7).
                      assert (H9 := tranS _ _ _ H6 H8).
                      rewrite H9 in H5. exact H5.
                (* s in Y *)
                apply H2; auto. 

       intros a H. 
       apply in_set_bop_reduce_union_intro. apply in_set_bop_reduce_union_elim in H. destruct H as [ H1 H2 ].
       destruct H1 as [L | R].
          split. left. apply in_set_minset_intro; auto. split; auto. intros s H. destruct (H2 s (inl H)); auto. 
          intros s [s_in_minX | s_in_Y].
             apply in_set_minset_elim in s_in_minX; auto. destruct s_in_minX as [s_in_X s_min]. 
             destruct (s_min a L); auto. 
             apply H2; auto. 
             split. right. exact R.
             intros s [s_in_minX | s_in_Y]. 
                apply H2. left. apply in_set_minset_elim in s_in_minX; auto. destruct s_in_minX as [s_in_X _]. exact s_in_X. 
                apply H2; auto.
Qed. 


Lemma bop_reduce_minset_commutative (X Y : finite_set S) : bop_reduce MS U X Y [=S] bop_reduce MS U Y X. 
Proof. unfold MS. unfold bop_reduce. 
       assert (K : (U X Y) [=S] (U Y X)). unfold U. apply bop_union_commutative; auto. 
       apply (minset_congruence _ _ K).
Qed.

Lemma bop_right_uop_minset_invariant : bop_right_uop_invariant (finite_set S) EQS (bop_reduce MS U) MS.
Proof. (* bop_reduce MS U (MS X) Y [=S] bop_reduce MS U X Y *)
       unfold bop_right_uop_invariant. intros X Y.
       assert (K1 : bop_reduce MS U X (MS Y) [=S] bop_reduce MS U (MS Y) X).
          apply bop_reduce_minset_commutative. 
       assert (K2 : bop_reduce MS U Y X [=S] bop_reduce MS U X Y).
          apply bop_reduce_minset_commutative.           
       assert (T1 := set_transitive _ _ _ K1 (bop_left_uop_minset_invariant Y X)). 
       assert (T2 := set_transitive _ _ _ T1 K2). exact T2. 
Qed. 

Lemma bop_minsert_union_is_reduce_union (X Y : finite_set S) : brel_set rS (bop_reduce MS U X Y) (MSU X Y) = true. 
Proof. apply r_left_and_right; auto.
       apply brel_set_symmetric; auto. 
       apply brel_set_transitive; auto. 
       apply bop_left_uop_minset_invariant. 
       apply bop_right_uop_minset_invariant.        
Qed.

Lemma big_eq (X Y : finite_set S) : (MS (MSU X Y)) [=S] (MS (U X Y)).
Proof.
       (* 
         MS (MSU X Y) 
        [=S] {def} 
         MS (MS (U (MS X) (MS Y)))
        [=S] {idem} 
         MS (U (MS X) (MS Y))
        [=S]  {bop_minsert_union_is_reduce_union, ...}
        MS (U X Y)
        *)
       assert (EQ1 : MS (MSU X Y) [=S] MS (MS (U (MS X) (MS Y)))).
          apply set_reflexive. 
       assert (EQ2 : MS (MS (U (MS X) (MS Y))) [=S] MS (U (MS X) (MS Y))).
          apply uop_minset_idempotent; auto. 
       assert (EQ3 : MS (U (MS X) (MS Y)) [=S] MS (U X Y)). 
          apply set_symmetric. apply bop_minsert_union_is_reduce_union. 
       assert (T1 := set_transitive _ _ _ EQ1 EQ2).
       assert (T2 := set_transitive _ _ _ T1 EQ3). exact T2. 
Qed. 


Lemma in_set_bop_minset_union_elim (a : S) (X Y : finite_set S) :
  a [in] (MSU X Y) ->
  ((a [in] (MS X) ) + (a [in] (MS Y) )) * (∀ s : S, s [in] (U (MS X) (MS Y)) → (a [=] s) + (s [!<=] a)). 
Proof. intro H. unfold bop_minset_union in H. unfold bop_reduce in H. unfold bop_full_reduce in H.
       apply in_set_minset_elim in H; auto. destruct H as [L R].
       apply in_set_bop_union_elim in L; auto. 
Qed. 

Lemma in_set_bop_minset_union_intro (a : S) (X Y : finite_set S) :
  ((a [in] (MS X) ) + (a [in] (MS Y) )) * (∀ s : S, s [in] (U (MS X) (MS Y)) → (a [=] s) + (s [!<=] a))
    -> a [in] (MSU X Y). 
Proof. intros [L_or_R H].
       unfold bop_minset_union; unfold bop_reduce; unfold bop_full_reduce.
       apply in_set_minset_intro; auto; split; auto.
       apply in_set_bop_union_intro; auto. 
Qed. 

Lemma bop_minset_union_associative : bop_associative (finite_set S) EQMS MSU. 
Proof. apply bop_full_reduce_associative_classical.
       apply brel_set_reflexive; auto.
       apply brel_set_symmetric; auto.
       apply brel_set_transitive; auto.       
       apply uop_minset_congruence; auto.
       apply uop_minset_idempotent; auto. 
       apply bop_union_congruence; auto.
       apply bop_union_associative; auto.
       apply bop_left_uop_minset_invariant.
       apply bop_right_uop_minset_invariant.
Qed. 


Lemma bop_minset_union_commutative : bop_commutative (finite_set S) EQMS MSU. 
Proof. apply bop_full_reduce_commutative.
       apply uop_minset_congruence; auto. 
       apply bop_union_commutative; auto. 
Qed. 

Lemma bop_minset_union_idempotent : bop_idempotent (finite_set S) EQMS MSU. 
Proof. apply bop_full_reduce_idempotent; auto.
       apply brel_set_transitive; auto. 
       apply uop_minset_congruence; auto. 
       apply uop_minset_idempotent; auto. 
       apply bop_union_idempotent; auto. 
Qed.


Lemma bop_minset_union_nil_left (X : finite_set S) : MSU nil X [=MS] X. 
Proof. unfold MSU. unfold bop_minset_union. unfold bop_full_reduce.
       rewrite uop_minset_nil. assert (K := bop_union_nil S rS refS symS tranS (uop_minset rS lteS X)).
       unfold EQMS. unfold brel_minset. unfold brel_reduce. 
       assert (J := minset_idempotent (bop_union rS nil (uop_minset rS lteS X))).
       assert (M := minset_idempotent X).        
       apply minset_congruence in K.
       assert (T1 := set_transitive _ _ _ J K).
       assert (T2 := set_transitive _ _ _ T1 M). exact T2. 
Qed.

Lemma bop_minset_union_nil_right (X : finite_set S) : MSU X nil [=MS] X. 
Proof. assert (J : MSU X nil [=MS] MSU nil X). apply bop_minset_union_commutative. 
       assert (K : MSU nil X [=MS] X). apply bop_minset_union_nil_left.
       apply (minset_transitive _ _ _ J K). 
Qed.


Lemma brel_minset_singleton_implies_is_minial_in (s : S) (X : finite_set S) : (s :: nil) [=MS] X -> is_minimal_wrt rS lteS s X = true.
Proof. intro H. unfold EQMS in H. unfold brel_minset in H. unfold brel_reduce in H. 
       apply brel_set_elim_prop in H; auto. destruct H as [L R]. 
       apply is_minimal_wrt_intro; auto. 
       intros s0 H1.
       case_eq(in_set rS (uop_minset rS lteS X) s0); intro J. 
          apply R in J. 
          apply in_set_minset_elim in J; auto. destruct J as [J _]. 
          apply in_set_singleton_elim in J; auto.  
          destruct (in_set_uop_minset_false_elim S rS wS f Pf congS refS symS tranS lteS lteCong lteRefl lteTrans s0 X H1 J)
                            as [s' [[H3 H4] H5]]. 
          assert (H6 := R s' H3). 
          apply in_set_minset_elim in H6; auto. destruct H6 as [H6 H7].           
          apply in_set_singleton_elim in H6; auto.            
          case_eq(lteS s0 s); intro H8; auto. 
          rewrite (lteCong _ _ _ _ (refS s0) H6) in H8. 
          rewrite (lteAntiSym _ _ H4 H8) in H5; auto. 
Qed. 


Lemma lemma1 (a s : S) (X : finite_set S) (P : s [in] X) (Q : (s :: nil) [=MS] X) (L : a [<=] s) : (a :: nil) [=MS] (a :: X). 
Proof. assert (M := brel_minset_singleton_implies_is_minial_in _ _ Q).
       apply brel_minset_intro; auto. 
       assert (H1 := is_minimal_wrt_elim S rS congS refS symS lteS lteCong s X M). 
       intro s0. split; intro H2.
          apply in_set_minset_singleton_elim in H2; auto. 
          apply in_set_minset_intro; auto. split. 
             apply in_set_cons_intro; auto.              
             intros s1 H3. apply in_set_cons_elim in H3; auto. destruct H3 as [H3 | H3]. 
                left. exact (tranS _ _ _ H2 H3). 
                destruct (H1 s1 H3) as [H4 | H4].
                   case_eq(rS s0 s1); intro H5; case_eq(lteS s1 s0); intro H6; auto. 
                      apply symS in H2. rewrite (lteCong _ _ _ _ H2 H4) in L.
                      rewrite (lteAntiSym _ _ L H6) in H5; auto. 
                   case_eq(rS s0 s1); intro H5; case_eq(lteS s1 s0); intro H6; auto. 
                      apply symS in H2. rewrite (lteCong _ _ _ _ H2 (refS s)) in L.
                      assert (H7 := lteTrans _ _ _ H6 L). rewrite H7 in H4; auto.                 
          apply in_set_minset_singleton_intro; auto. 
          apply in_set_minset_elim in H2; auto. 
          destruct H2 as [H2 H3].  apply in_set_cons_elim in H2; auto. 
          destruct H2 as [H2 | H2].           
             apply symS; auto. 
             destruct (H1 s0 H2) as [H4 | H4]. 
                assert (H5 : a [in] (a :: X)).  apply in_set_cons_intro; auto. 
                destruct (H3 a H5) as [H6 | H6]; auto. 
                   rewrite (lteCong _ _ _ _ (refS a) H4) in L. rewrite H6 in L; discriminate L. 

                assert (H5 : s [in] (a :: X)). apply in_set_cons_intro; auto. 
                destruct (H3 s H5) as [H6 | H6]; auto. 
                   rewrite (lteCong _ _ _ _ H6 (refS s)) in H4. rewrite lteRefl in H4. discriminate H4. 
                      (* s and s0 are incomparable *)
                      destruct (brel_minset_elim S rS symS tranS lteS _ _ Q s0) as [H7 H8].
                      assert (H9 : s0 [in] uop_minset rS lteS X).
                         apply in_set_minset_intro; auto. split; auto.
                         intros s1 H9.
                         assert (H10 : s1 [in] (a :: X)). apply in_set_cons_intro; auto.
                         exact (H3 s1 H10). 
                      assert (H10 := H8 H9). 
                      apply in_set_minset_singleton_elim in H10; auto. 
                      rewrite (lteCong _ _ _ _ H10 (refS s)) in H4. rewrite lteRefl in H4. discriminate H4. 
Qed. 

Lemma lemma2 (a s : S) (X : finite_set S) (P : s [in] X) (Q : (s :: nil) [=MS] X) (R : s [<=] a) : (s :: nil) [=MS] (a :: X).
Proof. assert (M := brel_minset_singleton_implies_is_minial_in _ _ Q).
       apply brel_minset_intro; auto. 
       assert (H1 := is_minimal_wrt_elim S rS congS refS symS lteS lteCong s X M).
       intro s0. split; intro H2; apply in_set_minset_elim in H2; auto; destruct H2 as [H2 H3].
          apply in_set_minset_intro; auto.
          apply in_set_singleton_elim in H2; auto.
          split.
             apply in_set_cons_intro; auto. right.
             rewrite <- (in_set_congruence S rS symS tranS s s0 _ _ (set_reflexive X) H2); auto. 
             intros s1 H4.
             apply in_set_cons_elim in H4; auto.
             destruct H4 as [H4 | H4]. 
                rewrite (lteCong _ _ _ _ (refS s) H4) in R. 
                case_eq(rS s0 s1); intro H5; case_eq(lteS s1 s0); intro H6; auto. 
                  rewrite (lteCong _ _ _ _ H2 (refS s1)) in R. 
                  assert (H7 := lteAntiSym _ _ R H6).  rewrite H7 in H5. discriminate H5. 
                destruct (H1 s1 H4) as [H5 | H5].
                   left. apply symS in H2. exact (tranS _ _ _ H2 H5). 
                   right. apply symS in H2. rewrite (lteCong _ _ _ _ (refS s1) H2). exact H5. 
             
          apply in_set_minset_singleton_intro; auto.
          assert (H4 : s [in] (a :: X)). apply in_set_cons_intro; auto.
          destruct (H3 s H4) as [H5 | H5]; auto. 
             apply in_set_cons_elim in H2; auto.
             destruct H2 as [H2 | H2]. 
                rewrite (lteCong _ _ _ _ (refS s) H2) in R. 
                rewrite H5 in R. discriminate R. 
                destruct (H1 s0 H2) as [H6 | H6].
                    apply symS; auto. 
                    (* s and s0 are incomparable *)
                      destruct (brel_minset_elim S rS symS tranS lteS _ _ Q s0) as [H7 H8].
                      assert (H9 : s0 [in] uop_minset rS lteS X).
                         apply in_set_minset_intro; auto. split; auto.
                         intros s1 H9.
                         assert (H10 : s1 [in] (a :: X)). apply in_set_cons_intro; auto.
                         exact (H3 s1 H10). 
                      assert (H10 := H8 H9). 
                      apply in_set_minset_singleton_elim in H10; auto. 
Qed. 

Lemma brel_minset_total_implies_trivial (T : brel_total S lteS) (X : finite_set S) : (X = nil) + {a : S & (a [in] X) * ((a::nil) [=MS] X)}. 
Proof. induction X; auto. right. 
       destruct IHX as [Xnil | [s [P Q]] ]. 
          exists a. split; rewrite Xnil. 
             compute. rewrite refS; auto. 
             apply minset_reflexive.
          destruct (T a s) as [L | R].
             exists a. split.
                apply in_set_cons_intro; auto.
                apply (lemma1 a s); auto. 
             exists s. split. 
                apply in_set_cons_intro; auto; right; auto.              
                apply (lemma2 a s); auto. 
Defined. 

Lemma bop_minset_union_signletons_left (x y : S) (H0: x [<=] y) : MSU (x :: nil) (y :: nil) [=MS] (x :: nil).
Proof. apply brel_minset_intro; auto. 
       intro s; split; intro H1; apply in_set_minset_elim in H1; auto; destruct H1 as [H1 H2]. 
          apply in_set_minset_singleton_intro; auto.
          apply in_set_bop_minset_union_elim in H1; auto. 
          destruct H1 as [H1 H3]. 
          destruct H1 as [H1 | H1]. 
             apply in_set_minset_singleton_elim in H1; auto. 

             apply in_set_minset_singleton_elim in H1; auto. 
             assert (H5 : x [in] U (MS (x :: nil)) (MS (y :: nil))).
                   apply in_set_bop_union_intro; auto. 
                   left. apply in_set_minset_singleton_intro; auto. 
             destruct (H3 x H5) as [H6 | H6]; auto. 
                   rewrite (lteCong _ _ _ _ (refS x) H1) in H6.
                   rewrite H6 in H0. discriminate H0.
                   
          apply in_set_singleton_elim in H1; auto. 
          apply in_set_minset_intro; auto.
          split. 
             apply in_set_bop_minset_union_intro; auto. 
             split. 
                left. apply in_set_minset_singleton_intro; auto.
                intros s0 H3. apply in_set_bop_union_elim in H3; auto. destruct H3 as [H3 | H3].
                   apply in_set_minset_singleton_elim in H3; auto. 
                   left. apply symS. exact (tranS _ _ _ H3 H1). 
                   apply in_set_minset_singleton_elim in H3; auto.               
                   case_eq(rS s s0); intro H4; case_eq(lteS s0 s); intro H5; auto. 
                      apply symS in H3. rewrite (lteCong _ _ _ _ H1 H3) in H0. 
                      rewrite (lteAntiSym _ _ H0 H5) in H4; auto. 
                   intros s0 H3. apply in_set_bop_minset_union_elim in H3; auto. destruct H3 as [H3 H4].
                   destruct H3 as [H3 | H3]. 
                      apply in_set_minset_singleton_elim in H3; auto. 
                      left. apply symS. exact (tranS _ _ _ H3 H1). 

                      apply in_set_minset_singleton_elim in H3; auto. 
                      case_eq(rS s s0); intro H5; case_eq(lteS s0 s); intro H6; auto. 
                         apply symS in H3. rewrite (lteCong _ _ _ _ H1 H3) in H0. 
                         rewrite (lteAntiSym _ _ H0 H6) in H5; auto. 
Qed. 
          
          

Lemma bop_minset_union_signletons_right (x y : S) (H: y [<=] x) : MSU (x :: nil) (y :: nil) [=MS] (y :: nil). 
Proof. assert (K : MSU (x :: nil) (y :: nil) [=MS] MSU (y :: nil) (x :: nil)).
          apply bop_minset_union_commutative. 
       assert (J : MSU (y :: nil) (x :: nil) [=MS] (y :: nil)).
          apply bop_minset_union_signletons_left; auto.
       apply (minset_transitive _ _ _ K J). 
Qed.        

Lemma bop_minset_union_selective : (brel_total S lteS) → bop_selective (finite_set S) EQMS MSU. 
Proof. intros T X Y. 
       destruct (brel_minset_total_implies_trivial T X) as [Xnil | [x [xInX EQx]] ];
       destruct (brel_minset_total_implies_trivial T Y) as [Ynil | [y [yInY EQy]] ].
          rewrite Xnil, Ynil. left. compute; auto. 
          rewrite Xnil. right. apply bop_minset_union_nil_left. 
          rewrite Ynil. left.  apply bop_minset_union_nil_right.
          assert (EQ1 : MSU (x :: nil) (y :: nil) [=MS] MSU X Y ). 
             apply (bop_minset_union_congruence _ _ _ _ EQx EQy).
             apply minset_symmetric in EQ1. 
          destruct (T x y) as [xy | yx]. 
             left. assert (EQ2 :  MSU (x :: nil) (y :: nil) [=MS] (x :: nil)). apply bop_minset_union_signletons_left; auto. 
                   assert (T1 := minset_transitive _ _ _ EQ1 EQ2).
                   assert (T2 := minset_transitive _ _ _ T1 EQx). exact T2. 
             right. assert (EQ2 :  MSU (x :: nil) (y :: nil) [=MS] (y :: nil)). apply bop_minset_union_signletons_right; auto. 
                    assert (T1 := minset_transitive _ _ _ EQ1 EQ2).
                    assert (T2 := minset_transitive _ _ _ T1 EQy). exact T2. 
Qed. 


Lemma bop_minset_union_not_selective : (brel_not_total S lteS) → bop_not_selective (finite_set S) EQMS MSU. 
Proof. intros [ [s t] [L R] ]. 
       exists (s :: nil, t :: nil).
       assert (t_in_minset : t [in] uop_minset rS lteS (bop_minset_union (s :: nil) (t :: nil))).
          apply in_set_minset_intro; auto. split. 
             apply in_set_bop_minset_union_intro; auto. split. 
                right. apply in_set_minset_singleton_intro; auto. 
                intros s0 H1. apply in_set_bop_union_elim in H1; auto. 
                destruct H1 as [H1 | H1].   
                  apply in_set_minset_singleton_elim in H1; auto.
                  right. apply symS in H1. rewrite (lteCong _ _ _ _ H1 (refS t)) in L. exact L. 
                  
                  apply in_set_minset_singleton_elim in H1; auto.
              intros s0 H1. 
              apply in_set_bop_minset_union_elim in H1; auto.
              destruct H1 as [H1 H2]. 
              destruct H1 as [H1 | H1].
                 apply in_set_minset_singleton_elim in H1; auto.
                 right. apply symS in H1. rewrite (lteCong _ _ _ _ H1 (refS t)) in L. exact L. 
                 apply in_set_minset_singleton_elim in H1; auto.
                 
       assert (s_in_minset : s [in] uop_minset rS lteS (bop_minset_union (s :: nil) (t :: nil))). 
          apply in_set_minset_intro; auto. split. 
             apply in_set_bop_minset_union_intro; auto. split. 
                left. apply in_set_minset_singleton_intro; auto. 
                intros s0 H1. apply in_set_bop_union_elim in H1; auto. 
                destruct H1 as [H1 | H1].   
                  apply in_set_minset_singleton_elim in H1; auto.
                  right. apply in_set_minset_singleton_elim in H1; auto.
                  apply symS in H1. rewrite (lteCong _ _ _ _ H1 (refS s)) in R. exact R. 

              intros s0 H1. 
              apply in_set_bop_minset_union_elim in H1; auto.
              destruct H1 as [H1 H2]. 
              destruct H1 as [H1 | H1].
                 apply in_set_minset_singleton_elim in H1; auto.
                 right. apply in_set_minset_singleton_elim in H1; auto.
                 apply symS in H1. rewrite (lteCong _ _ _ _ H1 (refS s)) in R. exact R. 
                 
       case_eq(EQMS (MSU (s :: nil) (t :: nil)) (s :: nil)); intro J1;
       case_eq(EQMS (MSU (s :: nil) (t :: nil)) (t :: nil)); intro J2; auto. 
             unfold MSU in J1. unfold EQMS in J1. unfold brel_minset in J1. unfold brel_reduce in J1. 
             apply brel_set_elim_prop in J1; auto. destruct J1 as [J1 _]. 
             assert (N := J1 t t_in_minset). 
             apply in_set_minset_elim in N; auto. destruct N as [N _]. 
             apply in_set_cons_elim in N; auto. destruct N as [N | N]. 
                rewrite (lteCong _ _ _ _ N (refS t)) in L. rewrite (lteRefl t) in L. discriminate L. 
                compute in N. discriminate N.

            (* same as case 1 *) 
            unfold MSU in J1. unfold EQMS in J1. unfold brel_minset in J1. unfold brel_reduce in J1. 
             apply brel_set_elim_prop in J1; auto. destruct J1 as [J1 _]. 
             assert (N := J1 t t_in_minset). 
             apply in_set_minset_elim in N; auto. destruct N as [N _]. 
             apply in_set_cons_elim in N; auto. destruct N as [N | N]. 
                rewrite (lteCong _ _ _ _ N (refS t)) in L. rewrite (lteRefl t) in L. discriminate L. 
                compute in N. discriminate N.
                
            unfold MSU in J2. unfold EQMS in J2. unfold brel_minset in J2. unfold brel_reduce in J2. 
             apply brel_set_elim_prop in J2; auto. destruct J2 as [J2 _]. 
             assert (N := J2 s s_in_minset). 
             apply in_set_minset_elim in N; auto. destruct N as [N _]. 
             apply in_set_cons_elim in N; auto. destruct N as [N | N]. 
                rewrite (lteCong _ _ _ _ N (refS s)) in R. rewrite (lteRefl s) in R. discriminate R. 
                compute in N. discriminate N. 
Defined. 




Lemma bop_minset_union_id_is_nil : bop_is_id (finite_set S) EQMS MSU nil.
Proof. unfold bop_is_id.  intro X; split. 
       apply bop_minset_union_nil_left. 
       apply bop_minset_union_nil_right.
Qed.

Lemma bop_minset_union_exists_id : bop_exists_id (finite_set S) EQMS MSU.
Proof. exists nil. apply bop_minset_union_id_is_nil. Defined.


Lemma needed_left (X : finite_set S) (bf : bottoms_finite S rS lteS) :
  (uop_minset rS lteS (U X ((fst (projT1 bf)) tt))) [=S] (MS ((fst (projT1 bf)) tt)).
Proof. destruct bf as [[fS w] P]. simpl.
       apply brel_set_intro_prop; auto. split.
          intros a H. apply in_set_minset_intro; auto. apply in_set_minset_elim in H; auto.
          destruct H as [L R]. apply in_set_bop_union_elim in L; auto.
          destruct L as [L | L]; split; auto.
             destruct (P a) as [P1 P2]. 
             assert (K := in_set_bop_union_intro S rS symS tranS X (fS tt) (w a)  (inr P1)). assert (J := R (w a) K). 
             destruct J as [J | J].
                assert (M : a [in] fS tt = w a [in] fS tt). apply symS in J. 
                    assert (N := in_set_congruence S rS symS tranS (w a) a _ _ (set_reflexive (fS tt)) J). rewrite N; auto. 
                 rewrite M; auto. 
                 rewrite P2 in J. discriminate J. 
             intros s H. assert (K := in_set_bop_union_intro S rS symS tranS X _ s (inr H)). exact (R s K). 
             intros s H. assert (K := in_set_bop_union_intro S rS symS tranS X _ s (inr H)). exact (R s K). 
          
          intros a H. apply in_set_minset_intro; auto. apply in_set_minset_elim in H; auto.
          destruct H as [L R]. split. 
             apply in_set_bop_union_intro; auto. 
             intros s H. apply in_set_bop_union_elim in H; auto. 
             destruct H as [H | H].
                destruct (P s) as [P1 P2]. assert (J := R (w s) P1).
                destruct J as [J | J]. 
                   case_eq(lteS s a); intro F; auto. left. 
                   assert (T := lteCong _ _ _ _ J (refS s)). rewrite P2 in T.
                   assert (W := lteAntiSym _ _ T F). exact W. 
                   case_eq(lteS s a); intro F; auto. left. 
                   case_eq(lteS a s); intro G.
                      assert (W := lteAntiSym _ _ G F). exact W. 
                      assert (T := lteTrans _ _ _ P2 F). rewrite J in T. discriminate T. 
                apply R; auto. 
Qed. 

Lemma needed_right (X : finite_set S) (bf : bottoms_finite S rS lteS) :
  brel_set rS (uop_minset rS lteS (bop_union rS ((fst (projT1 bf)) tt) X)) (uop_minset rS lteS ((fst (projT1 bf)) tt)) = true.
Proof. assert (EQ1 := bop_union_commutative S rS refS symS tranS (fst (projT1 bf) tt) X).
       assert (EQ2 := uop_minset_congruence S rS congS refS symS tranS lteS lteCong _ _ EQ1). 
       assert (EQ3 := needed_left X bf). 
       assert (T := set_transitive _ _ _ EQ2 EQ3). exact T.
Qed.

Lemma bop_minset_union_enum_is_ann (bf : bottoms_finite S rS lteS) : 
  bop_is_ann (finite_set S) (brel_minset rS lteS) bop_minset_union ((fst (projT1 bf)) tt).  
Proof. unfold bop_is_ann.
       intro X.
       assert (NL := needed_left X bf).               
       assert (NR := needed_right X bf).        
       destruct bf as [[fS w] P]. simpl. simpl in NL, NR. 
       split; unfold brel_minset; unfold brel_reduce; unfold bop_minset_union; unfold bop_full_reduce.             
       assert (EQ1 : brel_set rS (uop_minset rS lteS (uop_minset rS lteS (bop_union rS (uop_minset rS lteS (fS tt)) (uop_minset rS lteS X))))
                                 (uop_minset rS lteS (bop_union rS (uop_minset rS lteS (fS tt)) (uop_minset rS lteS X))) = true).
          apply minset_idempotent. 
       assert (EQ2 := bop_minsert_union_is_reduce_union (fS tt) X). 
          unfold bop_reduce in EQ2. unfold bop_minset_union in EQ2. unfold bop_full_reduce in EQ2.
          apply set_symmetric in EQ2.
       assert (T1 := set_transitive _ _ _ EQ1 EQ2).           
       assert (T2 := set_transitive _ _ _ T1 NR). exact T2. 

       assert (EQ1 : brel_set rS (uop_minset rS lteS (uop_minset rS lteS (bop_union rS (uop_minset rS lteS X) (uop_minset rS lteS (fS tt)))))
                                 (uop_minset rS lteS (bop_union rS (uop_minset rS lteS X) (uop_minset rS lteS (fS tt)))) = true).
          apply minset_idempotent. 
       assert (EQ2 := bop_minsert_union_is_reduce_union X (fS tt)). 
          unfold bop_reduce in EQ2. unfold bop_minset_union in EQ2. unfold bop_full_reduce in EQ2.
          apply set_symmetric in EQ2.
       assert (T1 := set_transitive _ _ _ EQ1 EQ2).           
       assert (T2 := set_transitive _ _ _ T1 NL). exact T2. 
Qed.        

Lemma bop_minset_union_exists_ann (bf : bottoms_finite S rS lteS) : 
   bop_exists_ann (finite_set S) (brel_minset rS lteS) bop_minset_union.
Proof. exists ((fst (projT1 bf)) tt).
       apply (bop_minset_union_enum_is_ann bf). 
Defined. 



Lemma bop_minset_union_not_exists_ann (bnf : bottoms_not_finite S rS lteS) : 
  bop_not_exists_ann (finite_set S) (brel_minset rS lteS) bop_minset_union.
Proof. destruct bnf as [F Q]. 
       unfold bop_not_exists_ann. intro X. unfold bop_not_is_ann.
       exists ((F X) :: nil). 
       right. unfold brel_minset. unfold brel_reduce.
       case_eq(brel_set rS (uop_minset rS lteS (bop_minset_union ((F X) :: nil) X)) (uop_minset rS lteS X)); intro J; auto.
          assert (K := big_eq ((F X) :: nil) X).  apply set_symmetric in K.
          assert (L := set_transitive _ _ _ K J). 
          apply brel_set_elim_prop in L; auto.  destruct L as [L R].
          assert (W : in_set rS (uop_minset rS lteS (bop_union rS ((F X) :: nil) X)) (F X) = true). 
             apply in_set_minset_intro; auto. split. 
                apply in_set_bop_union_intro; auto. left. compute. rewrite refS; auto. 
                intros a H.  apply in_set_bop_union_elim in H; auto.
                destruct H as [H | H].
                   compute in H. case_eq(rS a (F X)); intro T. apply symS in T. left. exact T. rewrite T in H. discriminate H. 
                   rewrite (Q X a H). right; auto. 
          assert (G := L (F X) W).
          apply in_set_minset_elim in G; auto. destruct G as [G1 G2].
          assert (N := Q X (F X) G1).  rewrite lteRefl in N. discriminate N. 
Defined. 



Definition bop_minset_union_exists_ann_decide (bf_d : bottoms_finite_decidable S rS lteS) :
      bop_exists_ann_decidable (finite_set S) (brel_minset rS lteS) bop_minset_union
 := match bf_d with
     | inl p  => inl (bop_minset_union_exists_ann p) 
     | inr p => inr (bop_minset_union_not_exists_ann p)
    end.

Definition bop_minset_union_selective_decide (tot_d : brel_total_decidable S lteS) : 
      bop_selective_decidable (finite_set S) (brel_minset rS lteS) bop_minset_union
 := match tot_d with
     | inl tot  => inl (bop_minset_union_selective tot) 
     | inr ntot => inr (bop_minset_union_not_selective ntot)
    end.


End Theory.

Section ACAS.

Definition sg_CI_proofs_minset_union : 
  ∀ (S : Type) (rS lteS : brel S) (s : S) (f : S -> S) ,
     brel_not_trivial S rS f ->     
     eqv_proofs S rS -> po_proofs S rS lteS -> 
        sg_CI_proofs (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS)
  := λ S rS lteS s f ntS eqvS poS,
let congS := A_eqv_congruence S rS eqvS in  
let refS := A_eqv_reflexive S rS eqvS in
let symS := A_eqv_symmetric S rS eqvS in
let tranS := A_eqv_transitive S rS eqvS in

let lteCong    := A_po_congruence S rS lteS poS in
let lteRefl    := A_po_reflexive S rS lteS poS in
let lteTran    := A_po_transitive S rS lteS poS in
let lteAntiSym := A_po_antisymmetric S rS lteS poS in 
let tot_d      := A_po_total_d S rS lteS poS in 
{|
  A_sg_CI_associative        := bop_minset_union_associative S rS s f ntS congS refS symS tranS lteS lteCong lteRefl lteTran lteAntiSym 
; A_sg_CI_congruence         := bop_minset_union_congruence S rS congS refS symS tranS lteS lteCong 
; A_sg_CI_commutative        := bop_minset_union_commutative S rS congS refS symS tranS lteS lteCong 
; A_sg_CI_idempotent         := bop_minset_union_idempotent S rS congS refS symS tranS lteS lteCong lteRefl
; A_sg_CI_selective_d        := bop_minset_union_selective_decide S rS s f ntS congS refS symS tranS lteS lteCong lteRefl lteTran lteAntiSym tot_d
|}. 

Definition A_sg_CI_minset_union : ∀ (S : Type),  A_po S -> A_sg_CI (finite_set S)
  := λ S po,
  let eqvS := A_po_eqv S po in
  let eqP  := A_eqv_proofs _ eqvS in
  let congS := A_eqv_congruence _ _ eqP in    
  let refS := A_eqv_reflexive _ _ eqP in
  let symS := A_eqv_symmetric _ _ eqP in
  let tranS := A_eqv_transitive _ _ eqP in
  let eq   := A_eqv_eq _ eqvS in  
  let s    := A_eqv_witness _ eqvS in
  let f    := A_eqv_new _ eqvS in
  let ntS  := A_eqv_not_trivial _ eqvS in
  let lteS := A_po_lte _ po in
  let poP  := A_po_proofs _ po in
  let lteCong    := A_po_congruence _ _ _ poP in
  let lteRefl    := A_po_reflexive _ _ _ poP in
  let lteTran    := A_po_transitive _ _ _ poP in
  let lteAntiSym := A_po_antisymmetric _ _ _ poP in 
  let bf_d := A_po_bottoms_finite_d _ _ _ poP in 
  {| 
     A_sg_CI_eqv          := A_eqv_minset S po
   ; A_sg_CI_bop          := bop_minset_union S eq lteS
   ; A_sg_CI_exists_id_d  := inl (bop_minset_union_exists_id S eq congS refS symS tranS lteS lteCong lteRefl)
   ; A_sg_CI_exists_ann_d := bop_minset_union_exists_ann_decide S eq s f ntS congS refS symS tranS lteS lteCong lteRefl lteTran lteAntiSym bf_d
   ; A_sg_CI_proofs       := sg_CI_proofs_minset_union S eq lteS s f ntS eqP poP 
   
   ; A_sg_CI_ast          := Ast_sg_minset_union (A_po_ast S po)                                                                   
  |}.

(*
    2) version of minset_union that takes a A_po_with_bottom 
    3) sg_CI_with_ann 
*)


End ACAS.

Section CAS.

Definition  check_minset_union_exists_ann {S : Type} (df_d : @check_bottoms_finite S) : @check_exists_ann (finite_set S)
  := match df_d with
     | Certify_Bottoms_Finite (f, _)  => Certify_Exists_Ann (f tt)
     | Certify_Is_Not_Bottoms_Finite => Certify_Not_Exists_Ann
     end.

Definition  check_minset_union_selective {S : Type} (tot_d : @check_total S) : @check_selective (finite_set S)
  := match tot_d with
     | Certify_Total            => Certify_Selective 
     | Certify_Not_Total (s, t) => Certify_Not_Selective (s :: nil, t :: nil)
     end.



Definition sg_CI_certs_minset_union : ∀ {S : Type},  @po_certificates S -> @sg_CI_certificates (finite_set S)
:= λ {S} po,  
{|
  sg_CI_associative        := Assert_Associative  
; sg_CI_congruence         := Assert_Bop_Congruence  
; sg_CI_commutative        := Assert_Commutative  
; sg_CI_idempotent         := Assert_Idempotent  
; sg_CI_selective_d        := check_minset_union_selective (po_total_d po)
|}. 

Definition sg_CI_minset_union : ∀ {S : Type}, @po S -> @sg_CI (finite_set S)
  := λ S po,
  let eqvS := po_eqv po   in
  let eq   := eqv_eq eqvS in  
  let lteS := po_lte po   in   
   {| 
     sg_CI_eqv       := eqv_minset po
   ; sg_CI_bop       := bop_minset_union S eq lteS 
   ; sg_CI_exists_id_d       := Certify_Exists_Id nil 
   ; sg_CI_exists_ann_d       := check_minset_union_exists_ann (po_bottoms_finite_d (po_certs po))
   ; sg_CI_certs     := sg_CI_certs_minset_union (po_certs po)
   
   ; sg_CI_ast       := Ast_sg_minset_union (po_ast po)                                                                   
   |}. 

End CAS.

Section Verify.

Lemma bop_minset_union_certs_correct 
      (S : Type) (eq lte : brel S) (s : S) (f : S -> S) (nt : brel_not_trivial S eq f) (eqv : eqv_proofs S eq) (po : po_proofs S eq lte) : 
      sg_CI_certs_minset_union (P2C_po S eq lte po) 
      =                        
      P2C_sg_CI (finite_set S) (brel_minset eq lte) (bop_minset_union S eq lte)
                (sg_CI_proofs_minset_union S eq lte s f nt eqv po).
Proof. destruct eqv, po. 
       unfold sg_CI_certs_minset_union, sg_CI_proofs_minset_union, P2C_sg_CI, P2C_po; simpl.
       destruct A_po_total_d as [tot | [[a b] [L R]]]; simpl; reflexivity. 
Qed. 
  

Theorem bop_minset_union_correct (S : Type) (po : A_po S) : 
         sg_CI_minset_union (A2C_po S po)  =  A2C_sg_CI (finite_set S) (A_sg_CI_minset_union S po). 
Proof. unfold sg_CI_minset_union, A_sg_CI_minset_union, A2C_sg_CI, A2C_po; simpl.
       rewrite <- bop_minset_union_certs_correct.
       rewrite <- correct_eqv_minset.
       destruct A_po_bottoms_finite_d as [[[F w] bf] | nbf];         
       reflexivity. 
Qed.
 
End Verify.   
  

