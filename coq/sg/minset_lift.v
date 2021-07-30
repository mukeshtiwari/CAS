
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures.

Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset.
Require Import CAS.coq.theory.order. (* for below, equiv, ... *) 

Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.
Require Import CAS.coq.sg.lift.

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

Variable bS : binary_op S. 
Variable bCong : bop_congruence S rS bS. 
Variable bAss : bop_associative S rS bS.
Variable bId  : bop_exists_id S rS bS.

(*
Variable LM : os_left_monotone S lteS bS. 
Variable RM : os_right_monotone S lteS bS. 
Variable DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS)). 
*) 

Definition bop_minset_lift : binary_op (finite_set S)
  := λ X Y, uop_minset lteS (bop_lift rS bS (uop_minset lteS X) (uop_minset lteS Y)). 



Notation "a [=] b"  := (rS a b = true)          (at level 15).
Notation "a [<>] b" := (rS a b = false)         (at level 15).
Notation "a <<= b"  := (lteS a b = true)        (at level 15).
Notation "a !<<= b" := (lteS a b = false)       (at level 15).
Notation "a << b"   := (below lteS b a = true) (at level 15).
Notation "a !<< b"  := (below lteS b a = false) (at level 15).
Notation "a [~] b"   := (equiv lteS b a = true) (at level 15).
Notation "a [!~] b"   := (equiv lteS b a = false) (at level 15).
Notation "a [#] b"   := (incomp lteS b a = true) (at level 15).
Notation "a [!#] b"   := (incomp lteS b a = false) (at level 15).
Notation "a [~|#] b"   := (equiv_or_incomp lteS b a = true) (at level 15).
Notation "a [!~|#] b"   := (equiv_or_incomp lteS b a = false) (at level 15).




Notation "a [in] b"  := (in_set rS b a = true)   (at level 15).
Notation "a [!in] b" := (in_set rS b a = false)  (at level 15).

Notation "a [=S] b"   := (brel_set rS a b = true)         (at level 15).
Notation "a [<>S] b"  := (brel_set rS a b = false)        (at level 15).
Notation "a [=MS] b"  := (brel_minset rS lteS a b = true)        (at level 15).
Notation "a [<>MS] b" := (brel_minset rS lteS a b = false)       (at level 15).
Notation "[ms] x" := (uop_minset lteS x) (at level 15).

Notation "a [^] b" := (bop_lift rS bS a b)         (at level 15).
Notation "a <^> b" := (bop_minset_lift a b)         (at level 15).

Definition set_transitive := brel_set_transitive S rS refS symS tranS.
Definition set_symmetric := brel_set_symmetric S rS.
Definition set_reflexive := brel_set_reflexive S rS refS symS.
Definition minset_idempotent := uop_minset_idempotent S rS refS symS tranS lteS lteCong lteRefl. 
Definition minset_transitive := brel_minset_transitive S rS refS symS tranS lteS.
Definition minset_symmetric := brel_minset_symmetric S rS lteS.
Definition minset_reflexive := brel_minset_reflexive S rS refS symS lteS.
Definition uop_minset_congruence_weak := uop_minset_congruence_weak _ _ refS symS tranS lteS lteCong lteRefl lteTrans. 
Definition uop_minset_congruence := uop_minset_congruence S rS refS symS tranS lteS lteCong.
Definition brel_minset_congruence_weak := brel_minset_congruence_weak S rS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition brel_minset_congruence := brel_minset_congruence S rS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition uop_minset_idempotent := uop_minset_idempotent _ _ refS symS tranS lteS lteCong lteRefl. 
Definition bop_lift_congruence := bop_lift_congruence _ _ bS refS tranS symS bCong. 
Definition bop_lift_associative := bop_lift_associative _ _ bS refS tranS symS bCong bAss. 
Definition set_equal_implies_minset_equal := set_equal_implies_minset_equal S rS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition below_pseudo_transitive_left := below_pseudo_transitive_left S lteS lteTrans. 
Definition below_pseudo_transitive_right := below_pseudo_transitive_right S lteS lteTrans.
Definition uop_minset_is_antichain := uop_minset_is_antichain S rS refS symS lteS lteCong lteRefl. 



Lemma bop_minset_lift_congruence : bop_congruence (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. unfold bop_congruence. intros X1 X2 Y1 Y2 A B.
       unfold bop_minset_lift.
       unfold brel_minset in A, B. 
       assert (C := bop_lift_congruence _ _ _ _ A B).
       assert (D := uop_minset_congruence_weak _ _ C).
       unfold brel_minset. 
       apply uop_minset_congruence_weak; auto. 
Qed.

Lemma minset_lift_commutative_weak (comm : bop_commutative S rS bS) (X Y : finite_set S) : ([ms] (X [^] Y)) [=MS] ([ms] (Y [^] X)). 
Proof. assert (A : (X [^] Y) [=S] (Y [^] X)).
          apply bop_lift_commutative; auto. 
       assert (B := uop_minset_congruence_weak _ _ A).
       apply uop_minset_congruence_weak; auto.
Qed. 

Lemma bop_minset_lift_commutative (comm : bop_commutative S rS bS) :
     bop_commutative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. intros X Y. unfold bop_minset_lift. apply minset_lift_commutative_weak; auto. Qed. 


Lemma bop_lift_singletons (s t : S) : ((s :: nil) [^] (t :: nil)) [=S] ((bS s t) :: nil).
Proof. compute.
       case_eq(rS (bS s t) (bS s t)); intro A; auto. 
       rewrite refS in A. discriminate A. 
Qed. 

Lemma bop_minset_lift_not_commutative (ncomm : bop_not_commutative S rS bS) :
     bop_not_commutative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. destruct ncomm as [[s t] A].
       exists (s :: nil, t ::nil).
       case_eq(brel_minset rS lteS ((s :: nil) <^> (t :: nil)) ((t :: nil) <^> (s :: nil))); intro B; auto. 
          unfold brel_minset in B. unfold bop_minset_lift in B.
          rewrite minset_singleton in B. rewrite minset_singleton in B. 
          assert (C := uop_minset_idempotent ((s :: nil) [^] (t :: nil))).  
          assert (D := uop_minset_idempotent ((t :: nil) [^] (s :: nil))).
          apply set_symmetric in C.
          assert (E := set_transitive _ _ _ C B). 
          assert (F := set_transitive _ _ _ E D). 
          assert (G := bop_lift_singletons s t). 
          assert (H := bop_lift_singletons t s). 
          assert (I : ([ms] ((s :: nil) [^] (t :: nil))) [=S] ((bS s t) :: nil)).
             assert (J := uop_minset_congruence_weak _ _ G).
             rewrite minset_singleton in J; auto. 
          assert (J : ([ms] ((t :: nil) [^] (s :: nil))) [=S] ((bS t s) :: nil)). 
             assert (J := uop_minset_congruence_weak _ _ G).
             rewrite minset_singleton in J; auto. 
          apply set_symmetric in I.
          assert (K := set_transitive _ _ _ I F).
          assert (L := set_transitive _ _ _ K J). 
          compute in L.  rewrite A in L. discriminate L. 
Defined. 


Definition bop_minset_lift_commutative_decide (comm_d : bop_commutative_decidable S rS bS) : 
  bop_commutative_decidable (finite_set S) (brel_minset rS lteS) bop_minset_lift := 
match comm_d with
| inl comm  => inl(bop_minset_lift_commutative comm)
| inr ncomm => inr(bop_minset_lift_not_commutative ncomm) 
end. 

Lemma minset_lift_right_inclusion_1
      (LM : os_left_monotone S lteS bS) 
      (RM : os_right_monotone S lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS)))
      (X Y : finite_set S) (a : S) (H : a [in] ([ms] (X [^] Y))) : 
     a [in] ([ms] (([ms] X) [^] Y)).
Proof. apply in_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_bop_lift_elim in H1; auto.
        destruct H1 as [x [y [[H3 H4] H5]]]. 
        apply in_minset_intro; auto. split.
           apply symS in H5. 
           rewrite (in_set_right_congruence S rS symS tranS (bS x y) a (([ms] X) [^] Y) H5);auto.
           case_eq(in_set rS ([ms] X) x); intro H6.
              apply in_set_bop_lift_intro; auto. 
              assert (B := H6). 
              apply in_set_minset_false_elim in B; auto.
              destruct B as [s [H7 H8]]. apply below_elim in H8.  destruct H8 as [H8 H9].
              assert (R := RM y _ _ H8).
              case_eq (lteS (bS x y) (bS s y)) ; intro H10. assert (H7' := H7). 
                 apply in_minset_elim in H7; auto. 
                 destruct H7 as [H7 H7'']. 
                 assert (H : (bS s y) [in] (X [^] Y)). apply in_set_bop_lift_intro; auto. 
                 assert (H11 := H2 _ H). 
                 apply symS in H5.
                 rewrite(below_congruence _ _ _ lteCong _ _ _ _ H5 (refS (bS s y))) in H11.
                 apply below_false_elim in H11. 
                 destruct H11 as [H11 | H11].
                    rewrite H11 in R. discriminate R.
                    destruct DDD as [AntiSym | [_ RSM]] .
                       (* AntiSym *) 
                       assert (G := AntiSym _ _ R H10).
                       rewrite (in_set_right_congruence S rS symS tranS _  _ (([ms] X) [^] Y) G); auto. 
                       apply in_set_bop_lift_intro; auto.
                       (* RSM *) 
                     destruct (RSM y  _  _ H8 H9) as [H12 H13].
                     rewrite H13 in H10. discriminate H10. 

                 assert (H11 : bS s y [in] (X [^] Y)).
                    apply in_set_bop_lift_intro; auto.
                    apply in_minset_elim in H7; auto.                     
                    destruct H7 as [H7 _]; auto. 
                 assert (Q := H2 (bS s y) H11). apply below_false_elim in Q.   destruct Q as [H12 | H12]. 
                    apply symS in H5. rewrite (lteCong _ _ _ _ (refS (bS s y)) H5) in H12.
                    rewrite H12 in R. discriminate R. 
                    apply symS in H5. rewrite (lteCong _ _ _ _ H5 (refS (bS s y))) in H12.
                    rewrite H12 in H10. discriminate H10.                    

           intros s H6.  apply H2. 
           apply in_set_bop_lift_elim in H6; auto.
           destruct H6 as [x' [y' [[H7 H8] H9]]].
           apply symS in H9. 
           rewrite (in_set_right_congruence S rS symS tranS (bS x' y') s (X [^] Y) H9);auto. 
           apply in_set_bop_lift_intro; auto.
           apply in_minset_elim in H7; auto. destruct H7 as [H7 _]; auto. 
Qed.            


(*
Lemma minset_lift_right_inclusion_1_VII
      (EEE : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_increasing S lteS bS) * (os_right_strictly_increasing S lteS bS)))
      (X Y : finite_set S) (a : S) (H : a [in] ([ms] (X [^] Y))) : 
     a [in] ([ms] (([ms] X) [^] Y)).
Proof. apply in_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_bop_lift_elim in H1; auto.
        destruct H1 as [x [y [[H3 H4] H5]]]. 
        apply in_minset_intro; auto. split.
           apply symS in H5. 
           rewrite (in_set_right_congruence S rS symS tranS (bS x y) a (([ms] X) [^] Y) H5);auto.
           case_eq(in_set rS ([ms] X) x); intro H6.
              apply in_set_bop_lift_intro; auto. 
              assert (B := H6). 
              apply in_set_minset_false_elim in B; auto.
              destruct B as [s [H7 H8]]. apply below_elim in H8.  destruct H8 as [H8 H9].
              assert (R := RM y _ _ H8).
              case_eq (lteS (bS x y) (bS s y)) ; intro H10. assert (H7' := H7). 
                 apply in_minset_elim in H7; auto. 
                 destruct H7 as [H7 _]. 
                 assert ((bS s y) [in] (X [^] Y)). apply in_set_bop_lift_intro; auto. 
                 assert (H11 := H2 _ H). 
                 apply symS in H5.
                 rewrite(below_congruence _ _ _ lteCong _ _ _ _ H5 (refS (bS s y))) in H11.
                 apply below_false_elim in H11. 
                 destruct H11 as [H11 | H11].
                    rewrite H11 in R. discriminate R.
                    destruct EEE as [AntiSym | [LSI RSI]] .
                       (* AntiSym *) 
                       assert (G := AntiSym _ _ R H10).
                       rewrite (in_set_right_congruence S rS symS tranS _  _ (([ms] X) [^] Y) G); auto. 
                       apply in_set_bop_lift_intro; auto.
                       (* SI *)
                       unfold os_left_strictly_increasing in LSI.
                       unfold os_right_strictly_increasing in RSI.
                       apply in_set_bop_lift_intro; auto.
                       case_eq(in_set rS ([ms] X) x); intro H14; auto.                     
                          apply in_set_minset_false_elim in H14; auto. 
                             destruct H14 as [t [H14 H15]]. 

admit.                              

                       
                 assert (H11 : bS s y [in] (X [^] Y)).
                    apply in_set_bop_lift_intro; auto.
                    apply in_minset_elim in H7; auto.                     
                    destruct H7 as [H7 _]; auto. 
                 assert (Q := H2 (bS s y) H11). apply below_false_elim in Q.   destruct Q as [H12 | H12]. 
                    apply symS in H5. rewrite (lteCong _ _ _ _ (refS (bS s y)) H5) in H12.
                    rewrite H12 in R. discriminate R. 
                    apply symS in H5. rewrite (lteCong _ _ _ _ H5 (refS (bS s y))) in H12.
                    rewrite H12 in H10. discriminate H10.                    

           intros s H6.  apply H2. 
           apply in_set_bop_lift_elim in H6; auto.
           destruct H6 as [x' [y' [[H7 H8] H9]]].
           apply symS in H9. 
           rewrite (in_set_right_congruence S rS symS tranS (bS x' y') s (X [^] Y) H9);auto. 
           apply in_set_bop_lift_intro; auto.
           apply in_minset_elim in H7; auto. destruct H7 as [H7 _]; auto. 
Admitted. 
*) 



(* nb : this did not use strictness or antisym *) 
Lemma minset_lift_right_inclusion_2
      (RM : os_right_monotone S lteS bS) 
      (X Y : finite_set S) (a : S) (H : a [in] ([ms] (([ms] X) [^] Y))) : 
  a [in] ([ms] (X [^] Y)).
Proof. apply in_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_bop_lift_elim in H1; auto.
        destruct H1 as [x [y [[H3 H4] H5]]]. 
        apply in_minset_intro; auto. split.
           apply in_minset_elim in H3; auto.
           destruct H3 as [H3 _].
           apply symS in H5. rewrite (in_set_right_congruence S rS symS tranS (bS x y) a (X [^] Y) H5);auto. 
           apply in_set_bop_lift_intro; auto. 

           intros s H6.
           apply in_set_bop_lift_elim in H6; auto. 
           destruct H6 as [b [ c [[H7 H8] H9]]].
           case_eq(in_set rS ([ms] X) b); intro H10. 
              apply H2.               
              apply symS in H9. rewrite (in_set_right_congruence S rS symS tranS (bS b c) s (([ms] X) [^] Y) H9);auto.
              apply in_set_bop_lift_intro; auto.
              apply in_set_minset_false_elim in H10; auto.
              destruct H10 as [b' [H11 H12]]. apply below_elim in H12. destruct H12 as [H12 H13].
              assert (H14 := RM c _ _ H12).
              assert (A : (bS b' c) [in] (([ms] X) [^] Y)).
                 apply in_set_bop_lift_intro; auto. 
              assert (B := H2 (bS b' c) A).
              case_eq(below lteS a s); intro C; auto. 
              apply below_false_elim in B. 
              rewrite(below_congruence _ _ _ lteCong _ _ _ _ H5 H9) in C.
              rewrite (lteCong _ _ _ _ (refS (bS b' c)) H5) in B. 
              rewrite (lteCong _ _ _ _ H5 (refS (bS b' c))) in B.               
              destruct B as [B | B].              
                 assert (D := below_pseudo_transitive_left _ _ _ H14 C). 
                 apply below_elim in D. destruct D as [D E].
                 rewrite D in B. discriminate B. 
                 assert (D := below_pseudo_transitive_right _ _ _ C B). 
                 apply below_elim in D. destruct D as [D E].
                 rewrite E in H14. discriminate H14. 
Qed.

(* note : clean these up someday?  *) 

Lemma minset_lift_left_invariant_v0
      (LM : os_left_monotone S lteS bS) 
      (RM : os_right_monotone S lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS)))      
       (X Y : finite_set S) :  [ms] (([ms] X) [^] Y) [=S] [ms] (X [^] Y). 
Proof. apply brel_set_intro_prop; auto. split.
       apply minset_lift_right_inclusion_2; auto.        
       apply minset_lift_right_inclusion_1; auto.        
Qed. 

Lemma minset_lift_left_invariant_v1
      (LM : os_left_monotone S lteS bS) 
      (RM : os_right_monotone S lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS)))      
      (X Y : finite_set S) :  [ms] (([ms] X) [^] Y) [=MS] [ms] (X [^] Y). 
Proof. assert (A := minset_lift_left_invariant_v0 LM RM DDD X Y).
       apply set_equal_implies_minset_equal; auto. 
Qed.


(* proves   (([ms] X) <^> Y) [=S] (X <^> Y)   *) 
Lemma minset_lift_left_invariant_v2 
      (LM : os_left_monotone S lteS bS) 
      (RM : os_right_monotone S lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS))): 
     bop_left_uop_invariant (finite_set S) (brel_set rS) bop_minset_lift (uop_minset lteS).
Proof. unfold bop_left_uop_invariant. intros X Y. 
       apply brel_set_intro_prop; auto. split. 
          intros a H.
          apply minset_lift_right_inclusion_2; auto. 
          intros a H.
          apply minset_lift_right_inclusion_1; auto. 
Qed.

(* (([ms] X) <^> Y) [=MS] (X <^> Y)   *) 
Lemma minset_lift_left_invariant
      (LM : os_left_monotone S lteS bS) 
      (RM : os_right_monotone S lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS))):       
     bop_left_uop_invariant (finite_set S) (brel_minset rS lteS) bop_minset_lift (uop_minset lteS).
Proof. intros X Y. 
       assert (A := minset_lift_left_invariant_v2 LM RM DDD X Y). 
       apply set_equal_implies_minset_equal; auto. 
Qed.




Lemma minset_lift_left_inclusion_1
      (LM : os_left_monotone S lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS)))
      (X Y : finite_set S) (a : S) (H : a [in] ([ms] (X [^] Y))) : 
  a [in] ([ms] (X [^] ([ms] Y))).
Proof. apply in_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_bop_lift_elim in H1; auto.
        destruct H1 as [x [y [[H3 H4] H5]]]. 
        apply in_minset_intro; auto. split.
            apply symS in H5. 
           rewrite (in_set_right_congruence S rS symS tranS (bS x y) a (X [^] ([ms] Y)) H5);auto.
           case_eq(in_set rS ([ms] Y) y); intro H6.
              apply in_set_bop_lift_intro; auto. 
              assert (B := H6). 
              apply in_set_minset_false_elim in B; auto.
              destruct B as [s [H7 H8]]. apply below_elim in H8. destruct H8 as [H8 H9]. 
              assert (R := LM x _ _ H8).
              case_eq (lteS (bS x y) (bS x s)) ; intro H10.
                 destruct DDD as [AntiSym | [LSM _]].
                    (* AntiSym *) 
                    assert (G := AntiSym _ _ R H10).
                    rewrite (in_set_right_congruence S rS symS tranS _  _ (X [^] ([ms] Y)) G); auto. 
                    apply in_set_bop_lift_intro; auto. unfold os_left_strictly_monotone in LSM.
                    (* LSM *) 
                  destruct (LSM x  _  _ H8 H9) as [H11 H12].
                  rewrite H12 in H10. discriminate H10. 
                    
                 assert (H11 : bS x s [in] (X [^] Y)).
                    apply in_set_bop_lift_intro; auto.
                    apply in_minset_elim in H7; auto.                     
                    destruct H7 as [H7 _]; auto.
                 assert (Q := H2 (bS x s) H11). 
                 apply below_false_elim in Q. 
                 destruct Q as [H12 | H12]. 
                    apply symS in H5. rewrite (lteCong _ _ _ _ (refS (bS x s)) H5) in H12.
                    rewrite H12 in R. discriminate R.
                    rewrite (lteCong _ _ _ _ (symS _ _ H5) (refS (bS x s))) in H12.
                    rewrite H12 in H10. discriminate H10.
           intros s H6.  apply H2. 
           apply in_set_bop_lift_elim in H6; auto.
           destruct H6 as [x' [y' [[H7 H8] H9]]].
           apply symS in H9. 
           rewrite (in_set_right_congruence S rS symS tranS (bS x' y') s (X [^] Y) H9);auto. 
           apply in_set_bop_lift_intro; auto.
           apply in_minset_elim in H8; auto. destruct H8 as [H8 _]; auto. 
Qed.            

(* nb : this did not use strictness or antisym *) 
Lemma minset_lift_left_inclusion_2
      (LM : os_left_monotone S lteS bS)
      (X Y : finite_set S) (a : S) (H : a [in] ([ms] (X [^] ([ms] Y)))) : 
  a [in] ([ms] (X [^] Y)).
Proof. apply in_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_bop_lift_elim in H1; auto.
        destruct H1 as [x [y [[H3 H4] H5]]]. 
        apply in_minset_intro; auto. split.
           apply in_minset_elim in H4; auto.
           destruct H4 as [H4 _].
           apply symS in H5. rewrite (in_set_right_congruence S rS symS tranS (bS x y) a (X [^] Y) H5);auto. 
           apply in_set_bop_lift_intro; auto. 

           intros s H6.
           apply in_set_bop_lift_elim in H6; auto. 
           destruct H6 as [b [ c [[H7 H8] H9]]].
           case_eq(in_set rS ([ms] Y) c); intro H10. 
              apply H2.               
              apply symS in H9. rewrite (in_set_right_congruence S rS symS tranS (bS b c) s (X [^] ([ms] Y)) H9);auto.
              apply in_set_bop_lift_intro; auto.
              apply in_set_minset_false_elim in H10; auto.
              destruct H10 as [c' [H11 H12]]. apply below_elim in H12. destruct H12 as [H12 H13].
              assert (H14 := LM b _ _ H12).
              assert (A : (bS b c') [in] (X [^] ([ms] Y))).
                 apply in_set_bop_lift_intro; auto. 
              assert (B := H2 (bS b c') A).
              rewrite (below_congruence _ _ _ lteCong _ _ _ _ H5 (refS (bS b c'))) in B.                 
              apply below_false_elim in B.
              destruct B as [B | B].
                 rewrite (below_congruence _ _ _ lteCong _ _ _ _ H5 H9). 
                 case_eq(below lteS (bS x y) (bS b c) ); intro D; auto. 
                    assert (E := below_pseudo_transitive_left _ _ _ H14 D).
                    apply below_elim in E. destruct E as [E F].
                     rewrite E in B. discriminate B. 
                 
                 assert (C := lteTrans _ _ _ B H14). 
                 rewrite (below_congruence _ _ _ lteCong _ _ _ _ H5 H9). 
                 case_eq(below lteS (bS x y) (bS b c) ); intro D; auto. 
                    assert (E := below_pseudo_transitive_right _ _ _ D C). 
                    assert (G := below_not_reflexive _ _ lteRefl (bS b c)). 
                    rewrite G in E. discriminate E. 
                 
Qed.



Lemma minset_lift_right_invariant_v0
      (LM : os_left_monotone S lteS bS) 
      (RM : os_right_monotone S lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS)))
      (X Y : finite_set S) :  [ms] (X [^] ([ms] Y)) [=S] [ms] (X [^] Y). 
Proof. apply brel_set_intro_prop; auto. split.
       apply minset_lift_left_inclusion_2; auto.        
       apply minset_lift_left_inclusion_1; auto.        
Qed. 

Lemma minset_lift_right_invariant_v1
      (LM : os_left_monotone S lteS bS) 
      (RM : os_right_monotone S lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS)))
      (X Y : finite_set S) :  [ms] (X [^] ([ms] Y)) [=MS] [ms] (X [^] Y). 
Proof. assert (A := minset_lift_right_invariant_v0 LM RM DDD X Y).
       apply set_equal_implies_minset_equal; auto. 
Qed.


Lemma minset_lift_right_invariant_v2
      (LM : os_left_monotone S lteS bS) 
      (RM : os_right_monotone S lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS))):       
     bop_right_uop_invariant (finite_set S) (brel_set rS) bop_minset_lift (uop_minset lteS).
Proof. unfold bop_right_uop_invariant. intros X Y. 
       apply brel_set_intro_prop; auto. split. 
          intros a H. apply minset_lift_left_inclusion_2; auto. 
          intros a H. apply minset_lift_left_inclusion_1; auto. 
Qed.

Lemma minset_lift_right_invariant
      (LM : os_left_monotone S lteS bS) 
      (RM : os_right_monotone S lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS))) :       
     bop_right_uop_invariant (finite_set S) (brel_minset rS lteS) bop_minset_lift (uop_minset lteS).
Proof. intros X Y. 
       assert (A := minset_lift_right_invariant_v2 LM RM DDD X Y). 
       apply set_equal_implies_minset_equal; auto. 
Qed.





(*       
Lemma bop_uop_minset_invariant (X Y : finite_set S): [ms] (([ms] X) [^] ([ms] Y)) [=MS] [ms] (X [^] Y). 
Proof.  assert (A : [ms] (([ms] X) [^] ([ms] Y)) [=MS] [ms] (X [^] ([ms] Y))).
          apply minset_lift_right_invariant. 
        assert (B := bop_right_uop_minset_invariant_right X Y).
        apply brel_minset_symmetric in B.   
        exact (minset_transitive _ _ _ A B). 
Qed.
 *)



Lemma bop_minset_lift_associative
      (LM : os_left_monotone S lteS bS) 
      (RM : os_right_monotone S lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
             ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS))):
  bop_associative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. intros X Y Z.
       assert (A : ((X <^> Y) <^> Z) [=MS] [ms] (([ms] (X <^> Y)) [^] ([ms] Z))).
           apply brel_minset_reflexive; auto. 
       assert (B : [ms] (([ms] (X <^> Y)) [^] ([ms] Z)) [=MS]  [ms] ((X <^> Y) [^] ([ms] Z))). 
           apply minset_lift_left_invariant; auto. 
       assert (C : ((X <^> Y) <^> Z) [=MS] [ms] ((X <^> Y) [^] ([ms] Z))). 
          exact (minset_transitive _ _ _ A B).
       assert (D : [ms] ((X <^> Y) [^] ([ms] Z))  [=MS] [ms] ([ms] (([ms] X) [^] ([ms] Y)) [^] ([ms] Z))). 
           apply brel_minset_reflexive; auto. 
       assert (E : ((X <^> Y) <^> Z) [=MS] [ms] ([ms] (([ms] X) [^] ([ms] Y)) [^] ([ms] Z))). 
          exact (minset_transitive _ _ _ C D).
          assert (F : [ms] (([ms] (([ms] X) [^] ([ms] Y))) [^] ([ms] Z)) [=MS] [ms] ((([ms] X) [^] ([ms] Y)) [^] ([ms] Z))).
             apply minset_lift_left_invariant_v1; auto. 
       assert (G : ((X <^> Y) <^> Z) [=MS] [ms] ((([ms] X) [^] ([ms] Y)) [^] ([ms] Z))).
          exact(minset_transitive _ _ _ E F).
       assert (H : [ms] ((([ms] X) [^] ([ms] Y)) [^] ([ms] Z)) [=MS] [ms] (([ms] X) [^] (([ms] Y) [^] ([ms] Z)))). 
          assert (AS := bop_lift_associative ([ms] X) ([ms] Y) ([ms] Z)).
          apply set_equal_implies_minset_equal in AS. 
          apply uop_minset_congruence; auto. 
       assert (I : ((X <^> Y) <^> Z) [=MS] [ms] (([ms] X) [^] (([ms] Y) [^] ([ms] Z)))).
          exact(minset_transitive _ _ _  G H).          
       assert (J : [ms] (([ms] X) [^] (([ms] Y) [^] ([ms] Z))) [=MS] [ms] (([ms] X) [^] ([ms] (([ms] Y) [^] ([ms] Z))))).  
           apply brel_minset_symmetric. 
           apply minset_lift_right_invariant_v1; auto. 
       assert (K : ((X <^> Y) <^> Z) [=MS] [ms] (([ms] X) [^] ([ms] (([ms] Y) [^] ([ms] Z))))).
          exact(minset_transitive _ _ _  I J).
       assert (L : [ms] (([ms] X) [^] ([ms] (([ms] Y) [^] ([ms] Z)))) [=MS] [ms] (([ms] X) [^] (Y <^> Z))).
          apply brel_minset_reflexive; auto. 
       assert (M : ((X <^> Y) <^> Z) [=MS] [ms] (([ms] X) [^] (Y <^> Z))).
          exact(minset_transitive _ _ _  K L).
       assert (N : [ms] (([ms] X) [^] (Y <^> Z)) [=MS] [ms] (([ms] X) [^] ([ms] (Y <^> Z)))).
           apply brel_minset_symmetric. 
           apply minset_lift_right_invariant_v1; auto. 
       assert (O : ((X <^> Y) <^> Z) [=MS] [ms] (([ms] X) [^] ([ms] (Y <^> Z)))).
          exact(minset_transitive _ _ _  M N).
       assert (P : [ms] (([ms] X) [^] ([ms] (Y <^> Z))) [=MS] (X <^> (Y <^> Z))). 
          apply brel_minset_reflexive; auto. 
       exact(minset_transitive _ _ _  O P).
Qed. 


Lemma bop_minset_lift_nil_left (X : finite_set S) :  (nil <^> X) [=MS] nil. 
Proof. unfold bop_minset_lift. unfold brel_minset.        
       rewrite minset_empty. compute; auto. 
Qed. 

Lemma bop_lift_nil_right (X : finite_set S) : (X [^] nil) [=S] nil.
Proof. destruct X.
       compute; auto. 
       apply brel_set_intro_prop; auto. split. 
          intros t A. apply in_set_bop_lift_elim in A; auto. 
          destruct A as [x [y [[B C] D]]]. 
          compute in C. discriminate C.        
          intros t A. compute in A. discriminate A.        
Qed.

Lemma bop_minset_lift_nil_right (X : finite_set S) : (X <^> nil) [=MS] nil.
Proof. unfold bop_minset_lift. unfold brel_minset.        
       rewrite minset_empty.
       assert (A := bop_lift_nil_right ([ms] X)). 
       assert (B := uop_minset_congruence_weak _ _ A).
       rewrite minset_empty in B. 
       assert (C := uop_minset_idempotent (([ms] X) [^] nil)). 
       exact (set_transitive _ _ _ C B). 
Qed. 

Lemma bop_minset_lift_ann_is_nil : bop_is_ann (finite_set S) (brel_minset rS lteS) bop_minset_lift nil. 
Proof. split. 
         apply bop_minset_lift_nil_left. 
         apply bop_minset_lift_nil_right.
Qed.

Lemma bop_minset_lift_exists_ann : bop_exists_ann (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists nil. apply bop_minset_lift_ann_is_nil. Defined.



Lemma bop_minset_lift_id_is_bottom
      (LM : os_left_monotone S lteS bS) 
      (RM : os_right_monotone S lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS)))
      (b : S) (P : bop_is_id S rS bS b) : 
      bop_is_id (finite_set S) (brel_minset rS lteS) bop_minset_lift (b :: nil). 
Proof. intro X.   
       destruct (bop_lift_is_id _ _ _ refS tranS symS bCong b P X) as [L R]. 
       unfold brel_minset. unfold bop_minset_lift.
       rewrite minset_singleton. split. 
          assert (A := uop_minset_idempotent ((b :: nil) [^] ([ms] X))). 
          assert (B := minset_lift_right_invariant_v0 LM RM DDD (b :: nil) X). 
          assert (C := set_transitive _ _ _ A B). 
          assert (D := uop_minset_congruence_weak _ _ L). 
          exact (set_transitive _ _ _ C  D). 

          assert (A := uop_minset_idempotent (([ms] X) [^] (b :: nil))). 
          assert (B := minset_lift_left_invariant_v0 LM RM DDD X (b :: nil) ). 
          assert (C := set_transitive _ _ _ A B). 
          assert (D := uop_minset_congruence_weak _ _ R).  
          exact (set_transitive _ _ _ C  D). 
Qed. 

Lemma bop_minset_lift_exists_id
      (LM : os_left_monotone S lteS bS) 
      (RM : os_right_monotone S lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
             ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS))) :
  bop_exists_id (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. destruct bId as [b P]. exists (b :: nil).
       apply bop_minset_lift_id_is_bottom; auto.
Defined. 


Lemma bop_minset_lift_not_is_left : bop_not_is_left (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists (wS :: nil, nil).
       unfold brel_minset. unfold bop_minset_lift.
       rewrite minset_singleton.  rewrite minset_empty. compute; auto. 
Defined. 


Lemma bop_minset_lift_not_is_right : bop_not_is_right (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists (nil, wS :: nil).
       unfold brel_minset. unfold bop_minset_lift.
       rewrite minset_singleton.  rewrite minset_empty. compute; auto. 
Defined. 


Lemma bop_minset_lift_not_anti_left : bop_not_anti_left (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists (nil, nil). compute; auto.  Defined. 

Lemma bop_minset_lift_not_anti_right : bop_not_anti_right (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists (nil, nil). compute; auto.  Defined.


Lemma uop_minset_equational_idempotence (X Y : finite_set S): 
  ([ms] ([ms] X)) [=S] ([ms] ([ms] Y)) -> ([ms] X) [=S] ([ms] Y). 
Proof. intro A.
       assert (B := minset_idempotent X). 
       assert (C := minset_idempotent Y).
       apply set_symmetric in B. 
       assert (D := set_transitive _ _ _ B A). 
       exact (set_transitive _ _ _ D C).        
Qed. 


Lemma bop_minset_lift_not_left_constant : bop_not_left_constant (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. unfold bop_not_left_constant.
       destruct bId as [b P].
       exists (b :: nil, (wS :: nil, (f wS) :: nil)).
       unfold brel_minset. unfold bop_minset_lift. 
       rewrite minset_singleton. rewrite minset_singleton. rewrite minset_singleton.
       case_eq(brel_set rS ([ms] ([ms] ((b :: nil) [^] (wS :: nil)))) ([ms] ([ms] ((b :: nil) [^] (f wS :: nil))))); intro A; auto. 
       apply uop_minset_equational_idempotence in A. 
       assert (B := bop_lift_singletons b wS).
       assert (C := bop_lift_singletons b (f wS)).       
       assert (D := uop_minset_congruence_weak _ _ B).
       assert (E := uop_minset_congruence_weak _ _ C).        
       assert (F := set_transitive _ _ _ A E).
       apply set_symmetric in D. 
       assert (G := set_transitive _ _ _ D F).
       rewrite minset_singleton in G. rewrite minset_singleton in G.
       compute in G.        
       assert (H : rS (bS b wS) (bS b (f wS)) = false). 
          destruct (Pf wS) as [I J].
          destruct (P wS) as [K L].     apply symS in K. 
          destruct (P (f wS)) as [M N]. apply symS in M. 
          rewrite (congS _ _ _ _ K M) in I; auto. 
       rewrite H in G.  discriminate G. 
Defined. 

       
Lemma bop_minset_lift_not_right_constant : bop_not_right_constant (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. unfold bop_not_right_constant.
       destruct bId as [b P].
       exists (b :: nil, (wS :: nil, (f wS) :: nil)).
       unfold brel_minset. unfold bop_minset_lift. 
       rewrite minset_singleton. rewrite minset_singleton. rewrite minset_singleton.
       case_eq(brel_set rS ([ms] ([ms] ((wS :: nil) [^] (b :: nil)))) ([ms] ([ms] ((f wS :: nil) [^] (b :: nil))))); intro A; auto. 
       apply uop_minset_equational_idempotence in A. 
       assert (B := bop_lift_singletons wS b).
       assert (C := bop_lift_singletons (f wS) b).       
       assert (D := uop_minset_congruence_weak _ _ B).
       assert (E := uop_minset_congruence_weak _ _ C).        
       assert (F := set_transitive _ _ _ A E).
       apply set_symmetric in D. 
       assert (G := set_transitive _ _ _ D F).
       rewrite minset_singleton in G. rewrite minset_singleton in G.
       compute in G.        
       assert (H : rS (bS wS b) (bS (f wS) b) = false). 
          destruct (Pf wS) as [I J].
          destruct (P wS) as [K L].     apply symS in L. 
          destruct (P (f wS)) as [M N]. apply symS in N. 
          rewrite (congS _ _ _ _ L N) in I; auto. 
       rewrite H in G.  discriminate G. 
Defined. 



Lemma bop_minset_lift_not_left_cancellative : bop_not_left_cancellative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. exists (nil, (wS :: nil, (f wS) :: nil)). 
       destruct (Pf wS) as [L R]. split. 
          compute; auto. 
          case_eq(brel_minset rS lteS (wS :: nil) (f wS :: nil)); intro F; auto.
          unfold brel_minset in F. 
          rewrite minset_singleton in F. rewrite minset_singleton in F. 
          compute in F. rewrite L in F. discriminate F. 
Defined. 


Lemma bop_minset_lift_not_right_cancellative : bop_not_right_cancellative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. exists (nil, (wS :: nil, (f wS) :: nil)). 
       destruct (Pf wS) as [L R]. split. 
          compute; auto. 
          case_eq(brel_minset rS lteS (wS :: nil) (f wS :: nil)); intro F; auto.
          unfold brel_minset in F. 
          rewrite minset_singleton in F. rewrite minset_singleton in F. 
          compute in F. rewrite L in F. discriminate F. 
Defined. 


(**************** selectivity, idempotence ***************) 

Lemma bop_minset_lift_not_selective_v1 
      (LM : os_left_monotone S lteS bS) 
      (RM : os_right_monotone S lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS))) :
         (bop_not_selective S rS bS) → bop_not_selective (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. intros [ [s t] [A B]]. 
       exists (s :: nil, t :: nil). 
          unfold bop_minset_lift.        
          unfold brel_minset. rewrite minset_singleton.  rewrite minset_singleton. split.
          case_eq(brel_set rS ([ms] ([ms] ((s :: nil) [^] ([ms] (t :: nil))))) (s :: nil)); intro C; auto. 
             assert (D := uop_minset_idempotent ((s :: nil) [^] ([ms] (t :: nil)))).
             assert (E := minset_lift_left_invariant_v0 LM RM DDD (s :: nil) (t :: nil)). 
             assert (F := bop_lift_singletons s t).
             assert (G := uop_minset_congruence_weak _ _ F). 
             rewrite minset_singleton in G. 
             assert (H := set_transitive _ _ _ E G).
             assert (I := set_transitive _ _ _ D H). apply set_symmetric in C. 
             assert (J := set_transitive _ _ _ C I).
             compute in J. rewrite A in J.
             case_eq(rS s (bS s t)); intro K. (* need better way of dealing with <> *) 
                apply symS in K. rewrite K in A. discriminate A. 
                rewrite K in J. discriminate J. 
          case_eq(brel_set rS ([ms] ([ms] ((s :: nil) [^] (t :: nil)))) (t :: nil)); intro C; auto. 
             assert (D := uop_minset_idempotent ((s :: nil) [^] ([ms] (t :: nil)))).
             assert (E := minset_lift_left_invariant_v0 LM RM DDD (s :: nil) (t :: nil)). 
             assert (F := bop_lift_singletons s t).
             assert (G := uop_minset_congruence_weak _ _ F). 
             rewrite minset_singleton in G. 
             assert (H := set_transitive _ _ _ E G).
             assert (I := set_transitive _ _ _ D H). apply set_symmetric in C. 
             assert (J := set_transitive _ _ _ C I).
             compute in J. rewrite B in J.
             case_eq(rS t (bS s t)); intro K. (* need better way of dealing with <> *) 
                apply symS in K. rewrite K in B. discriminate B. 
                rewrite K in J. discriminate J. 
Defined. 



Lemma bop_minset_lift_not_idempotent_v1 :
         (bop_not_idempotent S rS bS) → bop_not_idempotent (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. intros [ s A]. 
       exists (s :: nil). 
          unfold bop_minset_lift.        
          unfold brel_minset. rewrite minset_singleton.  
          case_eq(brel_set rS ([ms] ([ms] ((s :: nil) [^] (s :: nil)))) (s :: nil)); intro C; auto. 
             assert (D := uop_minset_idempotent ((s :: nil) [^] (s :: nil))).
             apply set_symmetric in D.
             assert (E := set_transitive _ _ _ D C). 
             apply brel_set_elim_prop in E; auto. destruct E as [E F]. 
             assert (G : s [in] (s :: nil)). apply in_set_cons_intro; auto. 
             assert (H := F s G). 
             apply in_minset_elim in H; auto. destruct H as [H I]. 
             apply in_set_bop_lift_elim in H; auto. 
             destruct H as [x [y [[J K] L]]].
             apply in_set_singleton_elim in K; auto.
             apply in_set_singleton_elim in J; auto.              
             assert (M : rS (bS s s) (bS x y) = true).
                exact (bCong _ _ _ _ J K). 
             apply symS in L. rewrite (tranS _ _ _ M L) in A. 
             discriminate A. 
Defined. 


Definition bop_strongly_selective (S : Type) (eq lte : brel S) (b : binary_op S) 
  := ∀ s t : S, ((eq (b s t) s = true) + (eq (b s t) t = true))
                + (  (below lte (b s t) s = true) 
                   * (below lte (b s t) t = true)
                   * ((incomp lte s t = true) + (equiv lte s t = true))                       
                   * ((eq (b t s) s = true) + (eq (b t s) t = true) + ((below lte (b t s) s = true) * (below lte (b t s) t = true)))). 

(*
Definition bop_not_strongly_selective (S : Type) (r : brel S) (b : binary_op S) 
    := { z : S * S & match z with (s, t) =>  (r (b s s) s = false) * (r (b t t) t = false) * (r (b s t) s = false)  * (r (b s t) t = false) end }. 

Lemma strongly_selective_implies_idempotent (r : brel S) (b : binary_op S) (ssel : bop_strongly_selective S r b) :
    bop_idempotent S r b. 
Proof. intros s. destruct (ssel s s) as [[[A | A] | A] | A]; auto. Qed. 

Lemma idempotent_implies_strongly_selective (r : brel S) (b : binary_op S) (idem : bop_idempotent S r b) :
    bop_strongly_selective S r b. 
Proof. intros s t. left. left. left. exact (idem s). Qed. 

Lemma not_strongly_selective_implies_not_idempotent (r : brel S) (b : binary_op S) (nssel : bop_not_strongly_selective S r b) :
    bop_not_idempotent S r b. 
Proof. destruct nssel as [[s t] [[[A B] C] D]]. exists s. auto. Defined. 

Lemma not_idempotent_implies_not_strongly_selective (r : brel S) (b : binary_op S) (nidem : bop_not_idempotent S r b) :
    bop_not_strongly_selective S r b. 
Proof. destruct nidem as [s A]. exists (s, s). auto. Defined. 
*) 

Lemma bop_minset_lift_idempotent_v1 (selS : bop_selective S rS bS) : bop_idempotent (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. intros X. unfold bop_minset_lift. unfold brel_minset. 
       assert (A := uop_minset_idempotent (([ms] X) [^] ([ms] X))). 
       assert (B := bop_lift_idempotent S rS bS refS tranS symS bCong selS ([ms] X)). 
       assert (C := set_equal_implies_minset_equal _ _ B). unfold brel_minset in C. 
       assert (D := uop_minset_idempotent X). 
       assert (E := set_transitive _ _ _ C D). 
       assert (F := set_transitive _ _ _ A E).
       exact F. 
Qed.

Lemma bop_minset_lift_idempotent_v2
      (idem : bop_idempotent S rS bS)
      (LI : os_left_increasing S lteS bS) 
      (RI : os_right_increasing S lteS bS) :  
         bop_idempotent (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. intros X. unfold bop_minset_lift. unfold brel_minset. 
       assert (A := uop_minset_idempotent (([ms] X) [^] ([ms] X))).
       assert (B : ([ms] (([ms] X) [^] ([ms] X))) [=S] ([ms] X)). 
         apply brel_set_intro_prop; auto. split. 
            intros s C. apply in_minset_elim in C; auto. 
            destruct C as [C D]. apply in_set_bop_lift_elim in C; auto. 
            destruct C as [x [y [[E F] G]]].
            case_eq(rS x y); intro H.
               admit. (* OK *)
               (* x <> y.  find contradiction or s in {x, y} *) 
               assert (I := LI x y). assert (J := RI y x).
               rewrite <- (lteCong _ _ _ _ (refS x) G) in I. 
               rewrite <- (lteCong _ _ _ _ (refS y) G) in J.
               assert (L : x [in] (([ms] X) [^] ([ms] X))). admit. 
               assert (M : y [in] (([ms] X) [^] ([ms] X))). admit.
               assert (N := D x L).
               assert (O := D y M).                   
               assert (K := uop_minset_is_antichain X x E y F). 
               apply equiv_or_incomp_elim in K. destruct K as [K | K]. 
                  (*x [~] y *) 
                  apply equiv_elim in K. destruct K as [K1 K2]. 
                  apply below_false_elim in N. 
                  apply below_false_elim in O. 
                  destruct N as [N | N]. 
                    rewrite I in N. discriminate N. 
                    destruct O as [O | O]. 
                       rewrite O in J. discriminate J. 
                       (* s ~ y ~ x.   x <> y *) 
                       case_eq(rS x s); intro P. 
                          admit. (* OK *)
                          case_eq(rS y s); intro Q. 
                             admit. (* OK *)
                             (* s ~ y ~ x.   x <> y  x <> s, y <> s   NEED **** here!!!   
                               
                              how about : x~y -> (bS x y) = x or (bS x y) = y.  like idempotence. 

                             *)
                             admit. 
                             

                  (*x [#] y *) 
                  apply below_false_elim in N. apply below_false_elim in O. 
                  destruct N as [N | N]. 
                     rewrite N in I. discriminate I. 
                     destruct O as [O | O].                   
                        rewrite O in J. discriminate J.
                        apply incomp_elim in K. destruct K as [K1 K2]. 
                        rewrite (lteTrans _ _ _ I O) in K1. 
                        discriminate K1. 
          intros s C. 
          apply in_minset_intro; auto. split. 
             admit. (* OK *) 
             intros t D. apply in_set_bop_lift_elim in D; auto. 
             destruct D as [x [y [[D E] F]]].              
             case_eq(below lteS s t); intro G; auto. 
                assert (H := LI x y). 
                assert (I := RI x y). 
                apply in_minset_elim in C; auto. destruct C as [C1 C2]. 
                apply in_minset_elim in D; auto. destruct D as [D1 D2]. 
                apply in_minset_elim in E; auto. destruct E as [E1 E2]. 
                rewrite <- (lteCong _ _ _ _ (refS x) F) in H.
                assert (J := C2 x D1).
                apply below_false_elim in J; auto. destruct J as [J | J]. 
                   assert (K : x << s). admit. 
                   apply below_elim in K; auto. destruct K as [K1 K2]. 
                   rewrite K1 in J. discriminate J.
                   assert (K : s <<= t). admit. 
                   apply below_elim in G; auto. destruct G as [G1 G2]. 
                   rewrite G2 in K. discriminate K.                 
       exact (set_transitive _ _ _ A B). 
Admitted. 




Lemma bop_minset_lift_not_idempotent_v2 
      (idem : bop_idempotent S rS bS)
      (NLI : os_not_left_increasing S lteS bS) :
            bop_not_idempotent (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. destruct NLI as [[s t] A]. 
       exists (s :: t :: nil). 
          unfold bop_minset_lift.        
          unfold brel_minset. 
          case_eq(brel_set rS ([ms] ([ms] (([ms] (s :: t :: nil)) [^] ([ms] (s :: t :: nil))))) ([ms] (s :: t :: nil))); intro C; auto. 
             assert (D := uop_minset_idempotent (([ms] (s :: t :: nil)) [^] ([ms] (s :: t :: nil)))). 
             apply set_symmetric in D.
             assert (E := set_transitive _ _ _ D C). 
             apply brel_set_elim_prop in E; auto. destruct E as [E F].
             assert (G : ([ms] (([ms] (s :: t :: nil)) [^] ([ms] (s :: t :: nil)))) [=S] ([ms] ((s :: t :: nil) [^] (s :: t :: nil)))). admit. 
             assert (H : ((s :: t :: nil) [^] (s :: t :: nil)) [=S] (s :: t :: (bS s t) :: (bS t s) :: nil)). admit. 
Admitted. 







(*  

(1) LOOK AT (+) of Martelli! 

X + Y = remove supersets {A union B | A in X,  B in Y}
X * Y = remove supersets (X union Y)

rm?   X subset Y -?-> X*Z subset Y*Z =  ms(X union Z) subset ms (Y union Z)  OK 


Is + idempotent?

X + X =?= X = ms(X) 

ms {A union B | A in X,  B in X} 
= 
ms [  union    {A} union {A union B | B in X and B <> A}  union {B union A | B in X and B <> A}  
     (A in X}  

a <= a * b 

and 

a <> b -> a < a * b

* comm 
* idem 

(2) look at upper sets 


st <> s
st <> t 

assume idempotent 

case 1: s = t. ***
case 2: s <> t, ss = s, tt = t 

   look at {s,t} {s,t} = {s, t, st, ts} 
 
   suppose ms({s, t, st, ts}) = {s,t} 

   then (1) s # t or s~t 
    and (2) s < st and t < st 
    and (3) ts in {s, t} or (s < ts and t < ts )

so I want the opposite of this 

           not(s # t or s~t)
         + not(s < st and t < st) 
         + not((ts in {s, t}) or (s < ts and t < ts ))

new property?  

  all s, (st = s + st = t) 
         + [ (s < st and t < st)  
            * (s # t or s~t)
            * ((ts in {s, t}) or (s < ts and t < ts ))]

simplify? 

*) 
Lemma bop_minset_lift_not_idempotent_v3 (idem : bop_idempotent S rS bS) (nselS : bop_not_selective S rS bS) :
       bop_not_idempotent (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. destruct nselS as [[s t] [A B]].
       unfold bop_not_idempotent. exists (s :: t :: nil). 
       case_eq(brel_minset rS lteS ((s :: t :: nil) <^> (s :: t :: nil)) (s :: t :: nil)); intro C; auto. 
          unfold brel_minset in C. unfold bop_minset_lift in C. 
          assert (D : ([ms] (([ms] (s :: t :: nil)) [^] ([ms] (s :: t :: nil)))) [=S] ([ms] (s :: t :: nil))).
             assert (E := uop_minset_idempotent (([ms] (s :: t :: nil)) [^] ([ms] (s :: t :: nil)))). 
             apply set_symmetric in E. 
             exact (set_transitive _ _ _ E C). 
         apply brel_set_elim_prop in D; auto. destruct D as [D E].
         case_eq(below lteS s t); intro F. 
Admitted.


End Theory.

Section ACAS.


(*  
Definition minset_lift_sg_proofs (S : Type) (eqS lteS : brel S) (bS : binary_op S)
                                                                                                
      (LM : os_left_monotone S lteS bS) 
      (RM : os_right_monotone S lteS bS) 
      (DDD : (brel_antisymmetric S eqS lteS) +
               ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS))): 
  sg_proofs (finite_set S) (brel_minset eqS lteS) (bop_minset_lift S eqS lteS bS) :=
let cngS := in   
let refS := in 
let symS := in 
let trnS := in
let lteCong := in 
let lteTran := in 
let bCong := in 
let bAss := in
let id := in
let wS := in
let f := in
let nt := in
let comm_d := in 
{|
  A_sg_associative      := bop_minset_lift_associative S eqS refS symS trnS lteS lteCong lteRefl lteTran bs bCong bAss LM RM DDD 
; A_sg_congruence       := bop_minset_lift_congruence S eqS refS symS trnS lteS lteCong lteRefl lteTran bs bCong

; A_sg_commutative_d    := bop_minset_lift_commutative_decide S eqS refS symS trnS lteS lteCong lteRefl lteTran bs bCong comm_d
; A_sg_selective_d      := 
; A_sg_idempotent_d     := 

; A_sg_is_left_d        := inr (bop_minset_lift_not_is_left S eqS lteS bS)
; A_sg_is_right_d       := inr (bop_minset_lift_not_is_right S eqS lteS bS)

; A_sg_left_cancel_d    := inr (bop_minset_lift_not_left_cancellative S eqS wS f nt lteS bS) 
; A_sg_right_cancel_d   := inr (bop_minset_lift_not_right_cancellative S eqS wS f nt lteS bS) 

; A_sg_left_constant_d  := inr (bop_minset_lift_not_left_constant S eqS wS f nt cngS refS symS trnS lteS lteCong lteRefl lteTran bs idS)
; A_sg_right_constant_d := inr (bop_minset_lift_not_right_constant S eqS wS f nt cngS refS symS trnS lteS lteCong lteRefl lteTran bs idS)

; A_sg_anti_left_d      := inr (bop_minset_lift_not_anti_left S eqS lteS bS)
; A_sg_anti_right_d     := inr (bop_minset_lift_not_anti_right S eqS lteS bS)

|}. 



Definition sg_CI_proofs_minset_lift_from_po : 
  ∀ (S : Type) (rS lteS : brel S) (s : S) (f : S -> S) ,
     brel_not_trivial S rS f ->     
     eqv_proofs S rS -> po_proofs S rS lteS -> 
        sg_CI_proofs (finite_set S) (brel_minset rS lteS) (bop_minset_lift S rS lteS)
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
  A_sg_CI_associative        := bop_minset_lift_associative S rS refS symS tranS lteS lteCong lteRefl lteTran 
; A_sg_CI_congruence         := bop_minset_lift_congruence S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_commutative        := bop_minset_lift_commutative S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_idempotent         := bop_minset_lift_idempotent S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_selective_d        := bop_minset_lift_selective_decide S rS s f ntS congS refS symS tranS lteS lteCong lteRefl lteTran tot_d
|}. 


Record msg_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_msg_associative      : bop_associative S eq bop                OK 
; A_msg_congruence       : bop_congruence S eq bop                 OK 
; A_msg_commutative_d    : bop_commutative_decidable S eq bop      OK 

(* needed?*)                                                    
; A_msg_is_left_d        : bop_is_left_decidable S eq bop          OK 
; A_msg_is_right_d       : bop_is_right_decidable S eq bop         OK 

(***)                                                   
; A_msg_left_cancel_d    : bop_left_cancellative_decidable S eq bop OK 
K; A_msg_right_cancel_d   : bop_right_cancellative_decidable S eq bop OK 
1
; A_msg_left_constant_d  : bop_left_constant_decidable S eq bop   OK 
; A_msg_right_constant_d : bop_right_constant_decidable S eq bop  OK 

; A_msg_anti_left_d      : bop_anti_left_decidable S eq bop       OK 
; A_msg_anti_right_d     : bop_anti_right_decidable S eq bop      OK 

                                                    
}. 







Definition sg_CI_proofs_minset_lift_from_qo : 
  ∀ (S : Type) (rS lteS : brel S) (s : S) (f : S -> S) ,
     brel_not_trivial S rS f ->     
     eqv_proofs S rS -> qo_proofs S rS lteS -> 
        sg_CI_proofs (finite_set S) (brel_minset rS lteS) (bop_minset_lift S rS lteS)
  := λ S rS lteS s f ntS eqvS qoS,
let congS := A_eqv_congruence S rS eqvS in  
let refS := A_eqv_reflexive S rS eqvS in
let symS := A_eqv_symmetric S rS eqvS in
let tranS := A_eqv_transitive S rS eqvS in

let lteCong    := A_qo_congruence S rS lteS qoS in
let lteRefl    := A_qo_reflexive S rS lteS qoS in
let lteTran    := A_qo_transitive S rS lteS qoS in
let lteNotAntiSym := A_qo_not_antisymmetric S rS lteS qoS in 
{|
  A_sg_CI_associative        := bop_minset_lift_associative S rS refS symS tranS lteS lteCong lteRefl lteTran 
; A_sg_CI_congruence         := bop_minset_lift_congruence S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_commutative        := bop_minset_lift_commutative S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_idempotent         := bop_minset_lift_idempotent S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_selective_d        := inr (brel_not_antisymmetric_implies_bop_minset_lift_not_selective S rS refS symS tranS lteS lteCong lteRefl lteTran lteNotAntiSym)
|}. 
*) 

(*
Definition A_sg_CI_minset_lift : ∀ (S : Type),  A_qo_with_bottom S -> A_sg_CI (finite_set S)
  := λ S qo,
  let eqvS := A_qowb_eqv S qo in
  let botP := A_qowb_exists_bottom S qo in 
  let eqP  := A_eqv_proofs _ eqvS in
  let congS := A_eqv_congruence _ _ eqP in    
  let refS := A_eqv_reflexive _ _ eqP in
  let symS := A_eqv_symmetric _ _ eqP in
  let tranS := A_eqv_transitive _ _ eqP in
  let eq   := A_eqv_eq _ eqvS in  
  let s    := A_eqv_witness _ eqvS in
  let f    := A_eqv_new _ eqvS in
  let ntS  := A_eqv_not_trivial _ eqvS in
  let lteS := A_qowb_lte _ qo in
  let poP  := A_qowb_proofs _ qo in
  let lteCong    := A_qo_congruence _ _ _ poP in
  let lteRefl    := A_qo_reflexive _ _ _ poP in
  let lteTran    := A_qo_transitive _ _ _ poP in

  {| 
     A_sg_CI_eqv          := A_eqv_minset S qo   HERE need eqv_minset built from qo ! *****************************
   ; A_sg_CI_bop          := bop_minset_lift S eq lteS
   ; A_sg_CI_exists_id_d  := inl (bop_minset_lift_exists_id S eq congS refS symS tranS lteS lteCong lteRefl)
   ; A_sg_CI_exists_ann_d := inl (bop_minset_lift_exists_ann S eq f ntS congS refS symS tranS lteS lteCong lteRefl lteTran botP)
   ; A_sg_CI_proofs       := sg_CI_proofs_minset_lift_from_qo S eq lteS s f ntS eqP poP 
   ; A_sg_CI_ast          := Ast_sg_minset_lift (A_po_ast S qo)                                                                   
  |}.

*) 

(*

from po:   with bottom? 

Definition A_sg_CI_minset_lift : ∀ (S : Type),  A_po S -> A_sg_CI (finite_set S)
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
   ; A_sg_CI_bop          := bop_minset_lift S eq lteS
   ; A_sg_CI_exists_id_d  := inl (bop_minset_lift_exists_id S eq congS refS symS tranS lteS lteCong lteRefl)
   ; A_sg_CI_exists_ann_d := bop_minset_lift_exists_ann_decide S eq s f ntS congS refS symS tranS lteS lteCong lteRefl lteTran lteAntiSym bf_d
   ; A_sg_CI_proofs       := sg_CI_proofs_minset_lift S eq lteS s f ntS eqP poP 
   
   ; A_sg_CI_ast          := Ast_sg_minset_lift (A_po_ast S po)                                                                   
  |}.




Why needed? 

    3) sg_CI_with_ann 
*) 


End ACAS.


(*
Section CAS.

Definition  check_minset_lift_exists_ann {S : Type} (df_d : @check_bottoms_finite S) : @check_exists_ann (finite_set S)
  := match df_d with
     | Certify_Bottoms_Finite (f, _)  => Certify_Exists_Ann (f tt)
     | Certify_Is_Not_Bottoms_Finite => Certify_Not_Exists_Ann
     end.

Definition  check_minset_lift_selective {S : Type} (tot_d : @check_total S) : @check_selective (finite_set S)
  := match tot_d with
     | Certify_Total            => Certify_Selective 
     | Certify_Not_Total (s, t) => Certify_Not_Selective (s :: nil, t :: nil)
     end.



Definition sg_CI_certs_minset_lift : ∀ {S : Type},  @po_certificates S -> @sg_CI_certificates (finite_set S)
:= λ {S} po,  
{|
  sg_CI_associative        := Assert_Associative  
; sg_CI_congruence         := Assert_Bop_Congruence  
; sg_CI_commutative        := Assert_Commutative  
; sg_CI_idempotent         := Assert_Idempotent  
; sg_CI_selective_d        := check_minset_lift_selective (po_total_d po)
|}. 

Definition sg_CI_minset_lift : ∀ {S : Type}, @po S -> @sg_CI (finite_set S)
  := λ S po,
  let eqvS := po_eqv po   in
  let eq   := eqv_eq eqvS in  
  let lteS := po_lte po   in   
   {| 
     sg_CI_eqv       := eqv_minset po
   ; sg_CI_bop       := bop_minset_lift S eq lteS 
   ; sg_CI_exists_id_d       := Certify_Exists_Id nil 
   ; sg_CI_exists_ann_d       := check_minset_lift_exists_ann (po_bottoms_finite_d (po_certs po))
   ; sg_CI_certs     := sg_CI_certs_minset_lift (po_certs po)
   
   ; sg_CI_ast       := Ast_sg_minset_lift (po_ast po)                                                                   
   |}. 

End CAS.
 *)

(*
Section Verify.

Lemma bop_minset_lift_certs_correct 
      (S : Type) (eq lte : brel S) (s : S) (f : S -> S) (nt : brel_not_trivial S eq f) (eqv : eqv_proofs S eq) (po : po_proofs S eq lte) : 
      sg_CI_certs_minset_lift (P2C_po S eq lte po) 
      =                        
      P2C_sg_CI (finite_set S) (brel_minset eq lte) (bop_minset_lift S eq lte)
                (sg_CI_proofs_minset_lift S eq lte s f nt eqv po).
Proof. destruct eqv, po. 
       unfold sg_CI_certs_minset_lift, sg_CI_proofs_minset_lift, P2C_sg_CI, P2C_po; simpl.
       destruct A_po_total_d as [tot | [[a b] [L R]]]; simpl; reflexivity. 
Qed. 
  

Theorem bop_minset_lift_correct (S : Type) (po : A_po S) : 
         sg_CI_minset_lift (A2C_po S po)  =  A2C_sg_CI (finite_set S) (A_sg_CI_minset_lift S po). 
Proof. unfold sg_CI_minset_lift, A_sg_CI_minset_lift, A2C_sg_CI, A2C_po; simpl.
       rewrite <- bop_minset_lift_certs_correct.
       rewrite <- correct_eqv_minset.
       destruct A_po_bottoms_finite_d as [[[F w] bf] | nbf];         
       reflexivity. 
Qed.
 
End Verify.   
  

*) 