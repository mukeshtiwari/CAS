
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



Lemma in_minset_intro (s : S) (X : finite_set S) :
  s [in] X -> (∀ (x : S), x [in] X -> x [!<] s) -> s [in] ([ms] X).
Admitted.   

Lemma in_minset_elim (s : S) (X : finite_set S) :
  s [in] ([ms] X) -> (s [in] X) * (∀ (x : S), x [in] X -> x [!<] s).
Admitted.   









   

(* associativity: 
  (a * b) * c 
= ms( ms(a .^ b) .^ c) 
= ms((a .^ b) .^ c) 
= ms(a .^ (b .^ c)) 
= ms(a .^ ms(b .^ c)) 
= a * (b * c) 

Need 

ms( ms(x) .^ y) = ms(x .^ y). 

Will uppersets help? 

up( up(x) .^ y) = up(x .^ y). 



*) 

(*
Print bop_left_uop_invariant.
bop_left_uop_invariant = 
λ (S : Type) (eq0 : brel S) (b : binary_op S) (r : unary_op S), ∀ s1 s2 : S, eq0 (b (r s1) s2) (b s1 s2) = true
     : ∀ S : Type, brel S → binary_op S → unary_op S → Prop
*) 


(* 
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

(*

*) 

Lemma test : bop_left_uop_invariant (finite_set S) (brel_set rS) (bop_reduce (uop_minset rS lteS) (bop_lift rS bS)) (uop_minset rS lteS).
Proof. unfold bop_left_uop_invariant. intros X Y. 
       apply brel_set_intro_prop; auto. split. 
          intros a H.
          unfold bop_reduce. unfold bop_reduce in H. 
          apply in_set_minset_elim in H; auto.  destruct H as [H1 H2]. 
          apply in_set_bop_lift_elim in H1; auto.
          destruct H1 as [x [y [[H3 H4] H5]]]. 
          apply in_set_minset_intro; auto. split. 
             rewrite (in_set_congruence S rS symS tranS _ _ _ _  (set_reflexive (X [lift] Y)) H5). 
             apply in_set_bop_lift_intro; auto. 
                apply in_set_minset_elim in H3; auto. destruct H3 as [H3 _]. exact H3. 
                intros s H6.
                apply in_set_bop_lift_elim in H6; auto. 
                destruct H6 as [x' [y' [[H6 H7] H8]]].
                case_eq(in_set rS ([ms] X) x'); intro H9.
                   assert (K : s [in] (([ms] X) [lift] Y)). admit.  (* OK *)   
                   apply (H2 s K).
                   case_eq (rS a s); intro F1; case_eq (lteS s a); intro F2; auto.
                   admit. (* ??? *) 









                   
                   Check in_set_uop_minset_false_elim. 

in_set_uop_minset_false_elim
     : ∀ (S : Type) (rS : brel S), S
                                   → ∀ fS : S → S, brel_not_trivial S rS fS
                                                   → brel_congruence S rS rS
                                                     → brel_reflexive S rS
                                                       → brel_symmetric S rS
                                                         → brel_transitive S rS
                                                           → ∀ lteS : brel S, brel_congruence S rS lteS
                                                                              → brel_reflexive S lteS
                                                                                → brel_transitive S lteS
                                                                                  → brel_antisymmetric S rS lteS
                                                                                    → ∀ (a : S) (X : finite_set S), in_set rS X a = true
                                                                                                                    → in_set rS (uop_minset rS lteS X) a =
                                                                                                                      false
                                                                                                                      → {s : S &
                                                                                                                        (in_set rS (uop_minset rS lteS X) s =
                                                                                                                         true) * 
                                                                                                                        (lteS s a = true) *
                                                                                                                        (rS s a = false)}

                

                find x'' in [ms] X with x'' <= x' 



                
                
                destruct (H2 _ K) as [L | R].
                   apply in_set_minset_elim in H3; auto. destruct H3 as [H3 H9]. 
                   destruct (H9 x' H6) as [L' | R'].
                      assert (K' := cong_bS _ _ _ _ L' (refS y')). 
                      assert (K'' := tranS _ _ _ L K').  apply symS in H8. 
                      left. exact (tranS _ _ _ K'' H8).

                      case_eq(rS a s); intro F1; case_eq(lteS s a); intro F2; auto.
(*
  L  : bS x  y [=] bS x y'
  R' : x' [!<=] x
  F1 : bS x y [!=] bS x' y'
  F2 : bS x' y' [<=] bS x y
  ============================
  (false = true) + (true = false)

??????????????????                      
*)
                         admit. 
                      
                      
                   right. case_eq(lteS s a); intro F; auto.
                   admit. (* need (bS x' y' [<=] bS x y) * (bS x y' [!<=] bS x y) *(x [<=] x') -> true=false 

   
                               x [<=] x' 
                               so bS x y' [<=] bS x' y'

                               so bS x y' [!<=] bS x' y'
                               VIOLATES monotonicity. 
*)
                
          intros a H. 
          unfold bop_reduce. unfold bop_reduce in H.
          apply in_set_minset_elim in H; auto. destruct H as [H1 H2]. 
          apply in_set_minset_intro; auto. split. 
             apply in_set_bop_lift_elim in H1; auto.            
             destruct H1 as [x [y [[H1 H3] H4]]]. 
             rewrite (in_set_congruence S rS symS tranS _ _ _ _  (set_reflexive (([ms] X) [lift] Y)) H4).                        
             apply in_set_bop_lift_intro; auto. 
                apply in_set_minset_intro; auto. split; auto. 
                intros s H5. 
                assert (K : (bS s y) [in] (X [lift] Y)). admit. 
                destruct (H2 _ K) as [L | R]. 
                   admit. (* need cancellation ?? ! *) 

                   right.  case_eq(lteS s x); intro F; auto.
(*
  R : bS s y [!<=] bS x y
  F : s [<=] x
  ============================
  true = false

  Need : monotonicity s [<=] x -> bS s y [<=] bS x y
*)                admit. 
                   
             intros s H3. 
             assert (K : s [in] (X [lift] Y)). admit. (* OK *) 
             apply H2; auto. 
Admitted.

Lemma bop_minset_lift_associative_classical :  bop_associative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. apply bop_full_reduce_associative_classical; auto. 
       apply set_reflexive. apply set_symmetric. apply set_transitive.
       apply uop_minset_congruence; auto.
       apply uop_minset_idempotent; auto.        
       apply bop_lift_congruence; auto.
       apply bop_lift_associative; auto.
       admit. 
       admit. 
Admitted.



Lemma bop_minset_lift_associative :  bop_associative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof.  intros X Y Z.
        apply brel_minset_intro; auto. 
        intro s; split; intro H1.
        unfold bop_minset_lift. unfold bop_full_reduce.
        unfold bop_minset_lift in H1. unfold bop_full_reduce in H1. 
Admitted. 

H1 : s [in] ([ms]
               ([ms]
                     (([ms]
                         ([ms]
                              (([ms] X) [lift] ([ms] Y))))
                     [lift]
                     ([ms] Z))
               )
            )

  ============================
  s [in] ([ms]
            ([ms]
               (([ms] X)
                  [lift]
                  ([ms]
                     ([ms]
                        (([ms] Y) [lift] ([ms] Z))
                     )
                  )
               )
            )
         )




Lemma bop_minset_lift_associative :  bop_associative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof.  intros X Y Z.
        apply brel_minset_intro; auto. 
        intro s; split; intro H1.
        (* H1 : s [in] ([ms] ((X [msl] Y) [msl] Z))
           ============================
           s [in] ([ms] (X [msl] (Y [msl] Z)))   *) 
        apply in_set_minset_intro; auto. 
        apply in_set_minset_elim in H1; auto. destruct H1 as [H1 sMinimal].
        apply in_set_minset_elim in H1; auto. destruct H1 as [H1 sMinimalInLift].
        apply in_set_bop_lift_elim in H1; auto. destruct H1 as [a [b [[aIn bIn] E]]].
        apply in_set_minset_elim in aIn; auto. destruct aIn as [aIn aMinimal].
        unfold bop_minset_lift in aIn.  unfold bop_full_reduce in aIn.
        apply in_set_minset_elim in aIn; auto.
        destruct aIn as [aIn aMinimal2].
        apply in_set_bop_lift_elim in aIn; auto.
        destruct aIn as [c [d [[xIn yIn] aEq] ]].        
        assert (E' : s [=] bS c (bS d b)).
           assert (K := cong_bS _ _ _ _ aEq (refS b)).
           assert (J := assoc_bS c d b).
           exact (tranS _ _ _ E (tranS _ _ _ K J)). 
        split. 
           rewrite (in_set_congruence  _ _ symS tranS _ _ _ _ (brel_set_reflexive _ _ refS symS (X [msl] (Y [msl] Z))) E').
           apply in_set_minset_intro; auto. split. 
              apply in_set_bop_lift_intro; auto. 
              apply in_set_minset_intro; auto. 
                 split. 
                    apply in_set_minset_intro; auto. split.
                       apply in_set_bop_lift_intro; auto. 
                       
                       intros s0 s0In. 
                       apply in_set_bop_lift_elim in s0In; auto. 
                       destruct s0In as [d' [b' [[d'In b'In] E'']]].
                       case_eq(rS (bS d b) s0); intro F1; case_eq(lteS s0 (bS d b)); intro F2; auto. 
                       admit.                        
                       
                    admit.
                        
              admit.

           admit.

           
        (* H1 : s [in] ([ms] (X [msl] (Y [msl] Z))) 
           ============================
           s [in] ([ms] ((X [msl] Y) [msl] Z))    *) 
        admit.               

Admitted.

       
Lemma bop_minset_lift_associative :  bop_associative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof.  intros X Y Z.
        apply brel_minset_intro; auto. 
        intro s; split; intro H1.
        (* H1 : s [in] ([ms] ((X [msl] Y) [msl] Z))
           ============================
           s [in] ([ms] (X [msl] (Y [msl] Z)))   *) 
        apply in_set_minset_intro; auto. 
        apply in_set_minset_elim in H1; auto. destruct H1 as [H1 sMinimal].
        apply in_set_minset_elim in H1; auto. destruct H1 as [H1 sMinimalInLift].
        apply in_set_bop_lift_elim in H1; auto. destruct H1 as [a [b [[aIn bIn] E]]].
        apply in_set_minset_elim in aIn; auto. destruct aIn as [aIn aMinimal].
        split. 
           (* show : s [in] (X [msl] (Y [msl] Z)) *)
           apply in_set_minset_intro; auto. 
           split. 
              (* s [in] (([ms] X) [lift] ([ms] (Y [msl] Z)))*) 
              unfold bop_minset_lift in aIn.  unfold bop_full_reduce in aIn. 
              apply in_set_minset_elim in aIn; auto.
              destruct aIn as [aIn aMinimal2].
              apply in_set_bop_lift_elim in aIn; auto.  
              destruct aIn as [c [d [[xIn yIn] aEq] ]].
              assert (E' : s [=] bS c (bS d b)). admit. 
              rewrite (in_set_congruence  _ _ symS tranS _ _ _ _ (brel_set_reflexive _ _ refS symS (([ms] X) [lift] ([ms] (Y [msl] Z)))) E').
              apply in_set_bop_lift_intro; auto.
              admit. 
              (* ∀ s0 : S, s0 [in] (([ms] X) [lift] ([ms] (Y [msl] Z))) → s [=] s0 + s0 [!<=] s *) 
              admit. 
           (* show :  ∀ s0 : S, s0 [in] (X [msl] (Y [msl] Z)) → s [=] s0 + s0 [!<=] s*)
           admit.
        (* H1 : s [in] ([ms] (X [msl] (Y [msl] Z))) 
           ============================
           s [in] ([ms] ((X [msl] Y) [msl] Z))    *) 
        admit.               

Admitted.


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

Record mm_minset_lift_proofs (S : Type) (eq : brel S) (bop : binary_op S) :=
{|
  A_mm_associative    :=
; A_mm_congruence     :=
; A_mm_exists_id      :=
; A_mm_commutative_d  :=
; A_mm_exists_ann_d   := 
; A_mm_left_cancel_d  := 
; A_mm_right_cancel_d := 
|}.



Section ACAS.

End ACAS.



Section CAS.

End CAS.



Section Verify.
 
End Verify.   
  

