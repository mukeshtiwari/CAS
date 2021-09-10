
Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset.
Require Import CAS.coq.theory.reduction.classical.
Require Import CAS.coq.theory.reduction.full.  
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.
Require Import CAS.coq.sg.union.
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
(*Variable lteAntiSym : brel_antisymmetric S rS lteS. *)

Variable bS : binary_op S.
Variable assoc_bS : bop_associative S rS bS. 
Variable cong_bS : bop_congruence S rS bS.

Definition bop_minset_lift : binary_op (finite_set S)
  := bop_full_reduce (uop_minset rS lteS) (bop_lift rS bS).

Notation "a [=] b"   := (rS a b = true)          (at level 15).
Notation "a [!=] b"  := (rS a b = false)          (at level 15).
Notation "a [=S] b"  := (brel_set rS a b = true)         (at level 15).
Notation "a [=MS] b" := (brel_minset rS lteS a b = true)        (at level 15).

Notation "a [in] b"  := (in_set rS b a = true)   (at level 15).
Notation "a [!in] b" := (in_set rS b a = false)   (at level 15).
Notation "a [<=] b"  := (lteS a b = true)        (at level 15).
Notation "a [!<=] b" := (lteS a b = false)       (at level 15).
Notation "a [!<] b"  := (not_below rS lteS b a =true)       (at level 15).

Notation  "a [msl] b"   := (bop_minset_lift a b) (at level 15).
Notation  "a [lift] b"  := (bop_lift rS bS a b) (at level 15).

Notation "[ms] a"          := (uop_minset rS lteS a) (at level 15).

Definition set_congruence := brel_set_congruence S rS refS symS tranS. 
Definition set_transitive := brel_set_transitive S rS refS symS tranS.
Definition set_symmetric := brel_set_symmetric S rS.
Definition set_reflexive := brel_set_reflexive S rS refS symS.
Definition minset_idempotent := uop_minset_idempotent S rS congS refS symS tranS lteS lteCong lteRefl. 
Definition minset_transitive := brel_minset_transitive S rS refS symS tranS lteS.
Definition minset_symmetric := brel_minset_symmetric S rS lteS.
Definition minset_reflexive := brel_minset_reflexive S rS refS symS lteS. 
Definition minset_congruence := uop_minset_congruence S rS congS refS symS tranS lteS lteCong.


Lemma in_set_bop_minset_lift_elim (a : S) (X Y : finite_set S) :
  a [in] (X [msl] Y) ->
  { b : S & { c : S & (a [=] (bS b c)) *
                      (b [in] ([ms] X)) *
                      (c [in] ([ms] Y)) *
                      (∀ s : S, s [in] (([ms] X) [lift] ([ms] Y)) → ((bS b c) [=] s) + (s [!<=] (bS b c)))}}.
Proof. intro H. unfold bop_minset_lift in H. unfold bop_reduce in H. unfold bop_full_reduce in H.
       apply in_set_minset_elim in H; auto. destruct H as [L R].
       apply in_set_bop_lift_elim in L; auto. destruct L as [x [y [[J K] M]]]. 
       exists x; exists y; split. split. split.
          exact M.
          exact J. 
          exact K. 
          intros s N. assert (P := R s N).
          destruct P as [P | P]. 
             left. rewrite <- (congS _ _ _ _ M (refS s)). exact P.
             right. rewrite <- (lteCong _ _ _ _ (refS s) M). exact P. 
Defined. 

Lemma in_set_bop_minset_lift_intro (a : S) (X Y : finite_set S) :
  { b : S & { c : S & (a [=] (bS b c)) *
                      (b [in] ([ms] X)) *
                      (c [in] ([ms] Y)) *
                      (∀ s : S, s [in] (([ms] X) [lift] ([ms] Y)) → ((bS b c) [=] s) + (s [!<=] (bS b c)))}}
    -> a [in] (X [msl] Y).
Proof. intros [b [x [[[E bInMinX] cInMinY] Q]]]. 
       unfold bop_minset_lift; unfold bop_reduce; unfold bop_full_reduce.
       apply in_set_minset_intro; auto; split; auto.
       rewrite (in_set_congruence _ _ symS tranS a (bS b x) _ _ (set_reflexive (([ms] X) [lift] ([ms] Y))) E). 
       apply in_set_bop_lift_intro; auto.
       intros s M. destruct (Q s M) as [P | P].
          left. rewrite (congS _ _ _ _ E (refS s)). exact P.
          right. rewrite (lteCong _ _ _ _ (refS s) E). exact P. 
Qed.

Lemma compute_minset_lift_singletons (x y : S) : ([ms] (([ms] (x :: nil)) [lift] ([ms] (y :: nil)))) [=S]  ((bS x y) :: nil).
Proof. rewrite uop_minset_singleton; auto. rewrite uop_minset_singleton; auto.
       assert (H1 : ((x :: nil) [lift] (y :: nil)) [=S] ((bS x y) :: nil)).           
             compute. rewrite refS. rewrite refS. reflexivity.
       apply minset_congruence in H1. 
       assert (H2 : ([ms] (bS x y :: nil)) [=S](bS x y :: nil)). 
          rewrite uop_minset_singleton; auto. apply set_reflexive. 
       exact (set_transitive _ _ _ H1 H2). 
Qed. 


Lemma bop_minset_lift_congruence : bop_congruence (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. apply bop_full_reduce_congruence. 
       apply (uop_minset_congruence _ _ congS refS symS tranS lteS lteCong). 
       apply bop_lift_congruence; auto. 
Qed.

Lemma bop_minset_lift_commutative : bop_commutative S rS bS -> bop_commutative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. intro H. 
       apply bop_full_reduce_commutative.
       apply uop_minset_congruence; auto. 
       apply bop_lift_commutative; auto. 
Qed.

Lemma bop_minset_lift_not_commutative  : bop_not_commutative S rS bS -> bop_not_commutative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. intros [[a b] P].
       exists (a :: nil, b::nil). unfold brel_minset. unfold brel_reduce. 
       unfold bop_minset_lift. unfold bop_full_reduce.
       case_eq(brel_set rS ([ms] ([ms] (([ms] (a :: nil)) [lift] ([ms] (b :: nil)))))
                           ([ms] ([ms] (([ms] (b :: nil)) [lift] ([ms] (a :: nil))))));
       intro J; auto.
       rewrite brel_set_minset_minset in J; auto.

       assert (Hab : ([ms] (([ms] (a :: nil)) [lift] ([ms] (b :: nil)))) [=S] ((bS a b) :: nil)).
          apply compute_minset_lift_singletons. 
          assert (Hba : ([ms] (([ms] (b :: nil)) [lift] ([ms] (a :: nil)))) [=S] ((bS b a) :: nil)).
          apply compute_minset_lift_singletons. 
          rewrite (set_congruence _ _ _ _ Hab Hba) in J.
          compute in J. 
          rewrite P in J. discriminate J. 
Qed. 



Lemma bop_minset_lift_nil_is_ann : bop_is_ann (finite_set S) (brel_minset rS lteS) bop_minset_lift nil.
Proof. unfold bop_is_ann. intro X. 
       unfold bop_minset_lift. unfold bop_full_reduce.
       rewrite uop_minset_nil. rewrite uop_minset_nil.
       rewrite bop_lift_nil_right.  compute; auto. 
Qed.        

Lemma bop_minset_lift_exists_ann : bop_exists_ann (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. exists nil. apply bop_minset_lift_nil_is_ann. Defined. 

Lemma bop_minset_lift_is_id (i : S) : bop_is_id S rS bS i  -> bop_is_id (finite_set S) (brel_minset rS lteS)  bop_minset_lift (i :: nil).
Proof. unfold bop_is_id.
       intros H X.
       unfold bop_minset_lift. unfold bop_full_reduce.
       rewrite uop_minset_singleton; auto. 
       split.
          apply brel_minset_intro; auto. intro s. split; intro H1. 
             apply in_set_minset_elim in H1; auto. destruct H1 as [H1 H2]. 
             apply in_set_minset_elim in H1; auto. destruct H1 as [H1 H3].
             apply in_set_bop_lift_elim in H1; auto.
             destruct H1 as [x [y [[H1 H4] H5]]].
             apply in_set_singleton_elim in H1; auto.
             assert (K : s [=] y).
                destruct (H y) as [L R].
                assert (K1 := cong_bS _ _ _ _ H1 (refS y)). apply symS in K1. 
                assert (K2 := tranS _ _ _ H5 K1). 
                exact (tranS _ _ _ K2 L). 
                
             rewrite (in_set_congruence S rS symS tranS s y _ _  (set_reflexive ([ms] X)) K). 
             exact H4.

             apply in_set_minset_intro; auto. split. 
                apply in_set_minset_intro; auto. split. 
                   assert (K : s [=] bS i s). destruct (H s) as [L _]; auto. 
                   rewrite (in_set_congruence S rS symS tranS _ _ _ _  (set_reflexive ((i :: nil) [lift] ([ms] X))) K). 
                   apply in_set_bop_lift_intro; auto. 
                      apply in_set_singleton_intro; auto. 
                   
                   intros s0 H2.
                   apply in_set_minset_elim in H1; auto. destruct H1 as [H1 H3]. 
                   assert (K : s0 [in] X).
                      apply in_set_bop_lift_elim in H2; auto.
                      destruct H2 as [x [y [[xIn yIn] E]]].
                      apply in_set_singleton_elim in xIn; auto.
                      assert (K := cong_bS _ _ _ _ xIn (refS y)).
                      destruct (H y) as [L R]. 
                      apply symS in K. 
                      assert (K' := tranS _ _ _ E (tranS _ _ _ K L)).                       
                      rewrite (in_set_congruence S rS symS tranS _ _ _ _  (set_reflexive X) K').
                      apply in_set_minset_elim in yIn; auto. destruct yIn as [yIn _].
                      exact yIn.                       
                   apply (H3 s0 K). 
                   
                intros s0 s0In.
                apply in_set_minset_elim in s0In; auto. destruct s0In as [s0In s0Minimal]. 
                apply in_set_bop_lift_elim in s0In; auto. 
                destruct s0In as [x [y [[xIn yIn] E]]]. 
                apply in_set_singleton_elim in xIn; auto. 
                apply in_set_minset_elim in H1; auto. destruct H1 as [H1 xMinimal]. 
                apply in_set_minset_elim in yIn; auto. destruct yIn as [yIn yMininal]. 
                assert (K : s0 [in] X).
                   assert (K1 := cong_bS _ _ _ _ xIn (refS y)). apply symS in K1. 
                   destruct (H y) as [L R]. 
                   assert (K2 := tranS _ _ _ E (tranS _ _ _ K1 L)). 
                   rewrite (in_set_congruence S rS symS tranS _ _ _ _  (set_reflexive X) K2).
                   exact yIn. 
                apply (xMinimal s0 K). 
                
        apply brel_minset_intro; auto. 
        intro s; split; intro sIn. 
           apply in_set_minset_elim in sIn; auto. destruct sIn as [sIn sMinimal]. 
           apply in_set_minset_elim in sIn; auto. destruct sIn as [sIn sMinimal'].
           apply in_set_bop_lift_elim in sIn; auto.
           destruct sIn as [x [y [[xIn yIn] E]]].
           apply in_set_singleton_elim in yIn; auto. 
           destruct (H x) as [L R].
           assert (K := cong_bS _ _ _ _ (refS x) yIn). apply symS in K. 
           assert (K' := tranS _ _ _ E (tranS _ _ _ K R)).
           rewrite (in_set_congruence S rS symS tranS _ _ _ _  (set_reflexive ([ms] X)) K').
           exact xIn.            

           apply in_set_minset_intro; auto. split. 
              apply in_set_minset_intro; auto. split. 
                 destruct (H s) as [L R]. apply symS in R. 
                 rewrite (in_set_congruence S rS symS tranS _ _ _ _  (set_reflexive (([ms] X) [lift] (i :: nil))) R).
                 apply in_set_bop_lift_intro; auto. 
                 apply in_set_singleton_intro; auto. 
                 
                 intros s0 s0In.
                 apply in_set_bop_lift_elim in s0In; auto. 
                 destruct s0In as [x [y [[xIn yIn] E]]].
                 apply in_set_minset_elim in sIn; auto. destruct sIn as [sIn sMinimal]. 
                 assert (K : s0 [in] X).
                    apply in_set_singleton_elim in yIn; auto.
                    destruct (H x) as [L R]. 
                    assert (K' := cong_bS _ _ _ _ (refS x) yIn). apply symS in K'.
                    assert (J := tranS _ _ _ E (tranS _ _ _ K' R)). 
                    apply in_set_minset_elim in xIn; auto. destruct xIn as [xIn _]. 
                    rewrite (in_set_congruence S rS symS tranS _ _ _ _  (set_reflexive X) J).
                    exact xIn.                     
                 apply (sMinimal s0 K). 
                 
              intros s0 s0In.
              apply in_set_minset_elim in s0In; auto. destruct s0In as [s0In s0Minimal]. 
              apply in_set_bop_lift_elim in s0In; auto.
              destruct s0In as [x [y [[xIn yIn] E]]].
              apply in_set_singleton_elim in yIn; auto. 
              assert (K := cong_bS _ _ _ _ (refS x) yIn). apply symS in K.
              destruct (H x) as [L R]. 
              assert (K' := tranS _ _ _ E (tranS _ _ _ K R)).
              apply in_set_minset_elim in sIn; auto. destruct sIn as [sIn sMinimal]. 
              assert (J : s0 [in] X).
                 apply in_set_minset_elim in xIn; auto. destruct xIn as [xIn _]. 
                 rewrite (in_set_congruence S rS symS tranS _ _ _ _  (set_reflexive X) K').
                 exact xIn. 
              apply (sMinimal s0 J). 
Qed. 
       
Lemma bop_minset_lift_exists_id : bop_exists_id S rS bS  -> bop_exists_id (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. intros [i P]. exists (i :: nil). apply bop_minset_lift_is_id; auto. Defined.

   

(* associativity: 
  (a * b) * c 
= ms( ms(a .^ b) .^ c) 
= ms((a .^ b) .^ c) 
= ms(a .^ (b .^ c)) 
= ms(a .^ ms(b .^ c)) 
= a * (b * c) 

Need 

ms( ms(x) .^ y) = ms(x .^ y). 

  if I is an identity, then 

  ms ((ms I) *^ (ms X)) =_MS X 

  ms ((ms I) *^ (ms {a})) =_MS {a} 

  ms ((ms I) *^ {a}) =_MS {a} 

  ms (ms ((ms I)) *^ {a}) = {a} 

  ms ((ms I) *^ {a}) = {a} 

  let (ms I) = {i1, i2, ... ik} 

  ms {i1 * a, i2 * a, ... ik *a}  = {a}  

  so, exists I' = {i1, i2, ... ik} st ms I' = I' (so i_s # i_t) 

  and for every a in S, 

  (1) ms {i1 * a, i2 * a, ... ik *a}  = {a}    
  (2) ms {a * i1, a * i2, ... a * ik}  = {a}    

 A simple example:
 
   S = {i1, i2, top} 
   I = {i1, i2}   
   
   top is annihilator 

   i1 * i1 = i1 
   i2 * i2 = i2

   i1 * i2 = i2 * i1 = top 

   i1 # i2,  i1 < top, i2 < top 

   easy to extend to     I = {i1, i2, i3, ... ik}   

   We will need a complex property in order to make "exists id" decidable. 

   Similar complexities arise with idempotence and selectivity. 

   current solution : construct only multiplicative monoids with minset_lift. 

 *)





  Lemma in_minset_intro (s : S) (X : finite_set S) :
  s [in] X -> (∀ (x : S), x [in] X -> x [!<] s) -> s [in] ([ms] X).
Admitted.   

Lemma in_minset_elim (s : S) (X : finite_set S) :
  s [in] ([ms] X) -> (s [in] X) * (∀ (x : S), x [in] X -> x [!<] s).
Admitted.   


Lemma in_set_uop_minset_false_elim_NEW (a : S) (X : finite_set S) :
  in_set rS X a = true -> in_set rS (uop_minset rS lteS X) a = false ->
  {s : S &   (in_set rS (uop_minset rS lteS X) s = true)
           * (lteS s a = true)
           * (lteS a s = false)}.
Admitted. 

Lemma minset_lift_right_inclusion_1
      (RM : os_right_monotone S lteS bS)
      (D : (brel_antisymmetric S rS lteS) + (os_right_strictly_monotone S lteS bS))      
      (X Y : finite_set S)
      (a : S)
      (H : a [in] ([ms] (X [lift] Y))) : 
  a [in] ([ms] (([ms] X) [lift] Y)).
Proof. apply in_set_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_bop_lift_elim in H1; auto.
        destruct H1 as [x [y [[H3 H4] H5]]]. 
        apply in_set_minset_intro; auto. split.
           apply symS in H5. 
           rewrite (in_set_right_congruence S rS symS tranS (bS x y) a (([ms] X) [lift] Y) H5);auto.
           case_eq(in_set rS ([ms] X) x); intro H6.
              apply in_set_bop_lift_intro; auto. 
              assert (B := H6). 
              apply in_set_uop_minset_false_elim_NEW in B; auto.
              destruct B as [s [[H7 H8] H9]].
              assert (R := RM y _ _ H8).
              case_eq (lteS (bS x y) (bS s y)) ; intro H10.
                 destruct D as [AntiSym | RSM].
                    (* AntiSym *) 
                    assert (G := AntiSym _ _ R H10).
                    rewrite (in_set_right_congruence S rS symS tranS _  _ (([ms] X) [lift] Y) G); auto. 
                    apply in_set_bop_lift_intro; auto.
                    (* RSM *) 
                  destruct (RSM y  _  _ H8 H9) as [H11 H12].
                  rewrite H12 in H10. discriminate H10. 
                    
                 assert (H11 : bS s y [in] (X [lift] Y)).
                    apply in_set_bop_lift_intro; auto.
                    apply in_minset_elim in H7; auto.                     
                    destruct H7 as [H7 _]; auto. 
                 destruct (H2 (bS s y) H11) as [H12 | H12]. 
                    apply symS in H5. rewrite (congS _ _ _ _ H5 (refS (bS s y))) in H12.
                    assert (H13 := lteRefl (bS s y)). 
                    apply symS in H12. 
                    rewrite (lteCong _ _ _ _ H12 (refS (bS s y))) in H13.
                    rewrite H13 in H10. discriminate H10.
                    rewrite (lteCong _ _ _ _ (refS (bS s y)) H5) in R.
                    rewrite R in H12. discriminate H12.
           intros s H6.  apply H2. 
           apply in_set_bop_lift_elim in H6; auto.
           destruct H6 as [x' [y' [[H7 H8] H9]]].
           apply symS in H9. 
           rewrite (in_set_right_congruence S rS symS tranS (bS x' y') s (X [lift] Y) H9);auto. 
           apply in_set_bop_lift_intro; auto.
           apply in_minset_elim in H7. destruct H7 as [H7 _]; auto. 
Qed.            

Lemma lte_implies_not_lt (AS: brel_antisymmetric S rS lteS) (x y : S) : x [<=] y -> not_below rS lteS x y = true.
Proof. intro H.
       unfold not_below. unfold bop_or. unfold uop_not.
       case_eq(lteS y x); intro F; auto.
       rewrite (AS _ _ F H). 
       compute; auto.
Qed.

Lemma minset_lift_right_inclusion_2
      (RM : os_right_monotone S lteS bS)
      (D : (brel_antisymmetric S rS lteS) + (os_right_strictly_monotone S lteS bS))            
      (X Y : finite_set S)
      (a : S)
      (H : a [in] ([ms] (([ms] X) [lift] Y))) : 
  a [in] ([ms] (X [lift] Y)).
Proof. apply in_set_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_bop_lift_elim in H1; auto.
        destruct H1 as [x [y [[H3 H4] H5]]]. 
        apply in_set_minset_intro; auto. split.
           apply in_minset_elim in H3; auto.
           destruct H3 as [H3 _].
           apply symS in H5. rewrite (in_set_right_congruence S rS symS tranS (bS x y) a (X [lift] Y) H5);auto. 
           apply in_set_bop_lift_intro; auto. 

           intros s H6.
           apply in_set_bop_lift_elim in H6; auto. 
           destruct H6 as [b [ c [[H7 H8] H9]]].
           case_eq(in_set rS ([ms] X) b); intro H10. 
              apply H2.               
              apply symS in H9. rewrite (in_set_right_congruence S rS symS tranS (bS b c) s (([ms] X) [lift] Y) H9);auto.
              apply in_set_bop_lift_intro; auto.

              apply in_set_uop_minset_false_elim_NEW in H10; auto.
              destruct H10 as [b' [[H11 H12] H13]].               
              assert (H14 := RM c _ _ H12).
              assert (A : (bS b' c) [in] (([ms] X) [lift] Y)).
                 apply in_set_bop_lift_intro; auto. 
              assert (B := H2 (bS b' c) A).
              case_eq(rS a s); intro C;
              case_eq(lteS s a); intro E; auto. 
              destruct B as [B | B].
                 rewrite (lteCong _ _ _ _ (symS _ _ B) (symS _ _ H9)) in H14.
                 destruct D as [AntiSym | RSM]. 
                 rewrite (AntiSym _ _ H14 E) in C. discriminate C. 
                 destruct (RSM c _ _ H12 H13) as [F1 F2].
                 rewrite (lteCong _ _ _ _ (symS _ _ H9) (symS _ _ B)) in F2.
                 rewrite F2 in E.  discriminate E. 
                 rewrite (lteCong _ _ _ _ H9 H5) in E.
                 rewrite (lteCong _ _ _ _ (refS (bS b' c)) H5) in B.                 
                 rewrite (lteTrans _ _ _ H14 E) in B.
                 discriminate B. 
Qed.




Lemma minset_lift_left_invariant 
      (RM : os_right_monotone S lteS bS)
      (D : (brel_antisymmetric S rS lteS) + (os_right_strictly_monotone S lteS bS)) :
     bop_left_uop_invariant (finite_set S) (brel_set rS) (bop_reduce (uop_minset rS lteS) (bop_lift rS bS)) (uop_minset rS lteS).
Proof. unfold bop_left_uop_invariant. intros X Y. 
       apply brel_set_intro_prop; auto. split. 
          intros a H.
          unfold bop_reduce. unfold bop_reduce in H.
          apply minset_lift_right_inclusion_2; auto. 
          intros a H.
          unfold bop_reduce. unfold bop_reduce in H.
          apply minset_lift_right_inclusion_1; auto. 
Qed.


Lemma minset_lift_left_inclusion_1
      (LM : os_left_monotone S lteS bS)
      (D : (brel_antisymmetric S rS lteS) + (os_left_strictly_monotone S lteS bS))      
      (X Y : finite_set S)
      (a : S)
      (H : a [in] ([ms] (X [lift] Y))) : 
  a [in] ([ms] (X [lift] ([ms] Y))).
Proof. apply in_set_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_bop_lift_elim in H1; auto.
        destruct H1 as [x [y [[H3 H4] H5]]]. 
        apply in_set_minset_intro; auto. split.
           apply symS in H5. 
           rewrite (in_set_right_congruence S rS symS tranS (bS x y) a (X [lift] ([ms] Y)) H5);auto.
           case_eq(in_set rS ([ms] Y) y); intro H6.
              apply in_set_bop_lift_intro; auto. 
              assert (B := H6). 
              apply in_set_uop_minset_false_elim_NEW in B; auto.
              destruct B as [s [[H7 H8] H9]].
              assert (R := LM x _ _ H8).
              case_eq (lteS (bS x y) (bS x s)) ; intro H10.
                 destruct D as [AntiSym | LSM].
                    (* AntiSym *) 
                    assert (G := AntiSym _ _ R H10).
                    rewrite (in_set_right_congruence S rS symS tranS _  _ (X [lift] ([ms] Y)) G); auto. 
                    apply in_set_bop_lift_intro; auto.
                    (* RSM *) 
                  destruct (LSM x  _  _ H8 H9) as [H11 H12].
                  rewrite H12 in H10. discriminate H10. 
                    
                 assert (H11 : bS x s [in] (X [lift] Y)).
                    apply in_set_bop_lift_intro; auto.
                    apply in_minset_elim in H7; auto.                     
                    destruct H7 as [H7 _]; auto. 
                 destruct (H2 (bS x s) H11) as [H12 | H12]. 
                    apply symS in H5. rewrite (congS _ _ _ _ H5 (refS (bS x s))) in H12.
                    assert (H13 := lteRefl (bS x s)). 
                    apply symS in H12. 
                    rewrite (lteCong _ _ _ _ H12 (refS (bS x s))) in H13.
                    rewrite H13 in H10. discriminate H10.
                    rewrite (lteCong _ _ _ _ (refS (bS x s)) H5) in R.
                    rewrite R in H12. discriminate H12.
           intros s H6.  apply H2. 
           apply in_set_bop_lift_elim in H6; auto.
           destruct H6 as [x' [y' [[H7 H8] H9]]].
           apply symS in H9. 
           rewrite (in_set_right_congruence S rS symS tranS (bS x' y') s (X [lift] Y) H9);auto. 
           apply in_set_bop_lift_intro; auto.
           apply in_minset_elim in H8. destruct H8 as [H8 _]; auto. 
Qed.            


Lemma minset_lift_left_inclusion_2
      (LM : os_left_monotone S lteS bS)
      (D : (brel_antisymmetric S rS lteS) + (os_left_strictly_monotone S lteS bS))      
      (X Y : finite_set S)
      (a : S)
      (H : a [in] ([ms] (X [lift] ([ms] Y)))) : 
  a [in] ([ms] (X [lift] Y)).
Proof. apply in_set_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_bop_lift_elim in H1; auto.
        destruct H1 as [x [y [[H3 H4] H5]]]. 
        apply in_set_minset_intro; auto. split.
           apply in_minset_elim in H4; auto.
           destruct H4 as [H4 _].
           apply symS in H5. rewrite (in_set_right_congruence S rS symS tranS (bS x y) a (X [lift] Y) H5);auto. 
           apply in_set_bop_lift_intro; auto. 

           intros s H6.
           apply in_set_bop_lift_elim in H6; auto. 
           destruct H6 as [b [ c [[H7 H8] H9]]].
           case_eq(in_set rS ([ms] Y) c); intro H10. 
              apply H2.               
              apply symS in H9. rewrite (in_set_right_congruence S rS symS tranS (bS b c) s (X [lift] ([ms] Y)) H9);auto.
              apply in_set_bop_lift_intro; auto.

              apply in_set_uop_minset_false_elim_NEW in H10; auto.
              destruct H10 as [c' [[H11 H12] H13]].               
              assert (H14 := LM b _ _ H12).
              assert (A : (bS b c') [in] (X [lift] ([ms] Y))).
                 apply in_set_bop_lift_intro; auto. 
              assert (B := H2 (bS b c') A).
              case_eq(rS a s); intro C;
              case_eq(lteS s a); intro E; auto. 
              destruct B as [B | B].
                 rewrite (lteCong _ _ _ _ (symS _ _ B) (symS _ _ H9)) in H14.
                 destruct D as [AntiSym | RSM]. 
                 rewrite (AntiSym _ _ H14 E) in C. discriminate C. 
                 destruct (RSM b _ _ H12 H13) as [F1 F2].
                 rewrite (lteCong _ _ _ _ (symS _ _ H9) (symS _ _ B)) in F2.
                 rewrite F2 in E.  discriminate E. 
                 rewrite (lteCong _ _ _ _ H9 H5) in E.
                 rewrite (lteCong _ _ _ _ (refS (bS b c')) H5) in B.                 
                 rewrite (lteTrans _ _ _ H14 E) in B.
                 discriminate B. 
Qed.


Lemma minset_lift_right_invariant 
      (LM : os_left_monotone S lteS bS)
      (D : (brel_antisymmetric S rS lteS) + (os_left_strictly_monotone S lteS bS)) :
     bop_right_uop_invariant (finite_set S) (brel_set rS) (bop_reduce (uop_minset rS lteS) (bop_lift rS bS)) (uop_minset rS lteS).
Proof. unfold bop_right_uop_invariant. intros X Y. 
       apply brel_set_intro_prop; auto. split. 
          intros a H.
          unfold bop_reduce. unfold bop_reduce in H.
          apply minset_lift_left_inclusion_2; auto. 
          intros a H.
          unfold bop_reduce. unfold bop_reduce in H.
          apply minset_lift_left_inclusion_1; auto. 
Qed.


Lemma bop_minset_lift_associative
      (LM : os_left_monotone S lteS bS)      
    (RM : os_right_monotone S lteS bS)
    (D : (brel_antisymmetric S rS lteS)
         + ((os_left_strictly_monotone S lteS bS) *
            (os_right_strictly_monotone S lteS bS))) :
       bop_associative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. apply bop_full_reduce_associative_classical; auto. 
       apply set_reflexive. apply set_symmetric. apply set_transitive.
       apply uop_minset_congruence; auto.
       apply uop_minset_idempotent; auto.        
       apply bop_lift_congruence; auto.
       apply bop_lift_associative; auto. 
       apply minset_lift_left_invariant; auto.
       destruct D as [AS | [_ RSM]]; auto. 
       apply minset_lift_right_invariant; auto.
       destruct D as [AS | [LSM _]]; auto. 
Qed. 


(* see how far the following can be pushed ... 
   Try to find weaker suff conditions .... 
*) 


Lemma conj4 (X Y : finite_set S) (a : S) : a [in] ([ms] X) -> a [in] ([ms] (X [msl] Y)). 
Admitted.

Lemma conj5 (Y Z : finite_set S) (b : S) : b [in] ([ms] (Y [msl] Z)) -> b [in] ([ms] Z).
Admitted.   

Lemma  conj3 (X Y Z : finite_set S) (s : S):
  s [in] (([ms] X) [lift] ([ms] (Y [msl] Z))) -> s [in] (([ms] (X [msl] Y)) [lift] ([ms] Z)). 
Proof. intro A. apply in_set_bop_lift_elim in A; auto. 
       destruct A as [a [b [[A B] C]]].
       rewrite (in_set_congruence _ _ symS tranS s (bS a b) _ _ (set_reflexive ((([ms] (X [msl] Y)) [lift] ([ms] Z)))) C).
       apply in_set_bop_lift_intro; auto.
       apply conj4; auto. 
       exact (conj5 Y Z b B).
Qed. 

Lemma  conj1 (X Y Z : finite_set S) (s : S):  s [in] ((X [msl] Y) [msl] Z) -> s [in] (X [msl] (Y [msl] Z)).
Proof. intro A.
       apply in_set_bop_minset_lift_elim in A.
       destruct A as [b [c [[[A B] C] D]]]. 
       apply in_set_bop_minset_lift_intro.
       case_eq(in_set rS ([ms] X) b); intro E; case_eq(in_set rS ([ms] (Y [msl] Z)) c); intro F.
          exists b; exists c; split; auto. 
          intros t G.
          assert (H : t [in] (([ms] (X [msl] Y)) [lift] ([ms] Z))).
             apply conj3; auto. 
          apply (D t H). 
          admit. (* b [in] ([ms] X), c [!in] ([ms] (Y [msl] Z)) *)           
          admit. (* b [!in] ([ms] X), c [in] ([ms] (Y [msl] Z)) *)
          admit. (* b [!in] ([ms] X), c [!in] ([ms] (Y [msl] Z)) *)                     
Admitted.    


Lemma  conj2 (X Y Z : finite_set S) (s : S):  s [in] (X [msl] (Y [msl] Z)) -> s [in] ((X [msl] Y) [msl] Z).
Admitted.

Lemma bop_minset_lift_associative_v2: 
  bop_associative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. intros X Y Z. 
       apply brel_minset_intro; auto. intro s. split. 
       intro A. 
       apply in_set_minset_elim in A; auto. destruct A as [A B].
       apply in_set_minset_intro; auto. split.
          apply conj1; auto. 
          intros t C.
          assert (D : t [in] ((X [msl] Y) [msl] Z)).
             apply conj2; auto. 
          assert (E := B t D). exact E. 
       intro A. 
       apply in_set_minset_elim in A; auto. destruct A as [A B].
       apply in_set_minset_intro; auto. split.
          apply conj2; auto. 
          intros t C.
          assert (D : t [in] (X [msl] (Y [msl] Z))).
             apply conj1; auto. 
          assert (E := B t D). exact E. 
Qed. 
       
Lemma bop_minset_lift_not_left_cancellative : bop_not_left_cancellative (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists (nil, (wS :: nil, (f wS) :: nil)). 
       destruct (Pf wS) as [L R]. split. 
          compute; auto. 
          case_eq(brel_minset rS lteS (wS :: nil) (f wS :: nil)); intro F; auto.
          destruct (brel_minset_elim _ _  symS tranS lteS _ _ F wS) as [H1 H2]. 
          assert (K : wS [in] ([ms] (wS :: nil))).
             rewrite (uop_minset_singleton S rS refS lteS lteRefl wS).
             apply in_set_singleton_intro; auto. 
          assert (J := H1 K).
          rewrite (uop_minset_singleton S rS refS lteS lteRefl (f wS)) in J.
          apply in_set_singleton_elim in J; auto.
          rewrite J in R.  exact R. 
Defined. 


Lemma bop_minset_lift_not_right_cancellative : bop_not_right_cancellative (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists (nil, (wS :: nil, (f wS) :: nil)). 
       destruct (Pf wS) as [L R]. split. 
          destruct (bop_minset_lift_nil_is_ann (wS :: nil)) as [H1 H2]. 
          destruct (bop_minset_lift_nil_is_ann ((f wS) :: nil)) as [H3 H4].
          apply minset_symmetric in H4. 
          exact (minset_transitive _ _ _ H2 H4). 
          
          case_eq(brel_minset rS lteS (wS :: nil) (f wS :: nil)); intro F; auto.
          destruct (brel_minset_elim _ _  symS tranS lteS _ _ F wS) as [H1 H2]. 
          assert (K : wS [in] ([ms] (wS :: nil))).
             rewrite (uop_minset_singleton S rS refS lteS lteRefl wS).
             apply in_set_singleton_intro; auto. 
          assert (J := H1 K).
          rewrite (uop_minset_singleton S rS refS lteS lteRefl (f wS)) in J.
          apply in_set_singleton_elim in J; auto.
          rewrite J in R.  exact R. 
Defined. 





End Theory.



(*

bop_minset_lift_associative
     : ∀ (S : Type) (rS : brel S), S
                                   → ∀ f : S → S, brel_not_trivial S rS f
                                                  → brel_congruence S rS rS
                                                    → brel_reflexive S rS
                                                      → brel_symmetric S rS
                                                        → brel_transitive S rS
                                                          → ∀ lteS : brel S, brel_congruence S rS lteS
                                                                             → brel_reflexive S lteS
                                                                               → brel_transitive S lteS
                                                                                 → ∀ bS : binary_op S, bop_associative S rS bS
                                                                                                       → bop_congruence S rS bS
                                                                                                         → os_left_monotone S lteS bS
                                                                                                           → os_right_monotone S lteS bS
                                                                                                             → brel_antisymmetric S rS lteS +
                                                                                                               os_left_strictly_monotone S lteS bS *
                                                                                                               os_right_strictly_monotone S lteS bS
                                                                                                               → bop_associative 
                                                                                                                   (finite_set S) 
                                                                                                                   (brel_minset rS lteS)
                                                                                                                   (bop_minset_lift S rS lteS bS)



bop_minset_lift_not_left_cancellative
     : ∀ (S : Type) (rS : brel S), S
                                   → ∀ f : S → S, brel_not_trivial S rS f
                                                  → brel_reflexive S rS
                                                    → brel_symmetric S rS
                                                      → brel_transitive S rS
                                                        → ∀ lteS : brel S, brel_reflexive S lteS
                                                                           → ∀ bS : binary_op S, bop_not_left_cancellative (finite_set S)
                                                                                                   (brel_minset rS lteS) (bop_minset_lift S rS lteS bS)

bop_minset_lift_not_right_cancellative
     : ∀ (S : Type) (rS : brel S), S
                                   → ∀ f : S → S, brel_not_trivial S rS f
                                                  → brel_reflexive S rS
                                                    → brel_symmetric S rS
                                                      → brel_transitive S rS
                                                        → ∀ lteS : brel S, brel_reflexive S lteS
                                                                           → ∀ bS : binary_op S, bop_not_right_cancellative (finite_set S)
                                                                                                   (brel_minset rS lteS) (bop_minset_lift S rS lteS bS)


*) 

(*
Record mm_minset_lift_proofs (S : Type) (eq : brel S) (bop : binary_op S) :=
{|
  A_mm_associative    :=
; A_mm_congruence     :=
; A_mm_exists_id      :=
; A_mm_exists_ann_d   :=     
; A_mm_commutative_d  :=
; A_mm_left_cancel_d  := 
; A_mm_right_cancel_d := 
|}.
*) 


Section ACAS.

End ACAS.



Section CAS.

End CAS.



Section Verify.
 
End Verify.   
  

