Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.theory.set. 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.theory.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.minset_union.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.minset_lift.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory. 

Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures.




Lemma os_left_strictly_monotone_implies_left_monotone (S : Type) (lte : brel S) (b : binary_op S):
  brel_reflexive S lte -> 
  os_left_strictly_monotone lte b ->
  bop_congruence S (equiv lte) b ->
     os_left_monotone lte b. 
Proof. intros refl LSM Cong s t u A.
       assert (lteRefl := equiv_reflexive S lte refl). 
       case_eq(lte u t); intro B.
          assert (C : equiv lte t u = true). apply equiv_intro; auto.       
          assert (D := Cong _ _ _ _ (lteRefl s) C).
          apply equiv_elim in D; auto.  destruct D as [D E]. exact E. 
          destruct (LSM s t u A B) as [C D]. exact C. 
Qed.


Lemma os_right_strictly_monotone_implies_right_monotone (S : Type) (lte : brel S) (b : binary_op S):
  brel_reflexive S lte -> 
  os_right_strictly_monotone lte b ->
  bop_congruence S (equiv lte) b ->
     os_right_monotone lte b. 
Proof. intros refl RSM Cong s t u A.
       assert (lteRefl := equiv_reflexive S lte refl). 
       case_eq(lte u t); intro B.
          assert (C : equiv lte t u = true). apply equiv_intro; auto.       
          assert (D := Cong _ _ _ _ C (lteRefl s)).
          apply equiv_elim in D; auto.  destruct D as [D E]. exact E. 
          destruct (RSM s t u A B) as [C D]. exact C. 
Qed.


Section Theory.

Variable S  : Type. 
Variable rS : brel S.

Variable wS : S.
Variable fS : S -> S.                
Variable Pf : brel_not_trivial S rS fS. 

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

(*
Variable LM : os_left_monotone S lteS bS. (* ∀ s t u : S, lteS t u = true → lteS (bS s t) (bS s u) = true  *) 
Variable RM : os_right_monotone S lteS bS. 
*) 


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

Notation "a [U] b" := (bop_union rS a b)         (at level 15).
Notation "a <U> b" := (bop_minset_union S rS lteS a b)         (at level 15).

Notation "a [^] b" := (bop_lift rS bS a b)         (at level 15).
Notation "a <^> b" := (bop_minset_lift S rS lteS bS a b)         (at level 15).


Definition set_congruence := brel_set_congruence S rS refS symS tranS.
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
Definition set_equal_implies_minset_equal := set_equal_implies_minset_equal S rS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition minset_union_left_uop_invariant_weak := minset_union_left_uop_invariant_weak S rS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition minset_union_right_uop_invariant_weak := minset_union_right_uop_invariant_weak S rS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition minset_union_uop_invariant_weak := minset_union_uop_invariant_weak S rS refS symS tranS lteS lteCong lteRefl lteTrans.

(* 
Definition bop_union_congruence := bop_union_congruence _ _ refS symS tranS.
Definition bop_union_idempotent := bop_union_idempotent _ _ refS symS tranS.
Definition bop_union_commutative := bop_union_commutative _ _ refS symS tranS.
Definition bop_union_associative := bop_union_associative _ _ refS symS tranS.
Definition bop_lift_congruence := bop_lift_congruence _ _ bS refS tranS symS bCong. 
Definition bop_lift_associative := b_lift_associative _ _ bS refS tranS symS bCong bAss. 
*) 

(***************** Assorted Lemmas ********************************)

(* used in minset_union_lift_left_left_absorptive_increasing_weak *) 
Lemma lift_left_increasing 
      (inc : os_left_increasing lteS bS) 
      (X Y : finite_set S):    
  (∀ (t : S), t [in] (X [^] Y) -> {x : S & (x [in] X) * (lteS x t = true)}).
Proof. intros t A.   unfold os_left_increasing in inc. 
       apply in_set_bop_lift_elim in A; auto. 
       destruct A as [x [y [[B C] D]]].
       exists x. split; auto. 
          rewrite (lteCong _ _ _ _ (refS x) D). exact (inc x y). 
Qed.        

(* used in minset_union_lift_left_right_absorptive_increasing_weak *) 
Lemma lift_right_increasing 
      (inc : os_right_increasing lteS bS) 
      (X Y : finite_set S):    
  (∀ (t : S), t [in] (Y [^] X) -> {x : S & (x [in] X) * (lteS x t = true)}).
Proof. intros t A.   
       apply in_set_bop_lift_elim in A; auto. 
       destruct A as [x [y [[B C] D]]].
       exists y. split; auto. 
          rewrite (lteCong _ _ _ _ (refS y) D). exact (inc y x). 
Qed.        

(* used in 
minset_union_lift_left_left_absorptive_increasing_weak and 
minset_union_lift_left_right_absorptive_increasing_weak
*)
Lemma union_left_antisymmetric 
      (anti: brel_antisymmetric S rS lteS)
      (X Y : finite_set S):    
      (∀ (y : S), y [in] Y -> {x : S & (x [in] X) * (lteS x y = true)})
      -> ([ms] X) [=S] ([ms] (X [U] Y)).
Proof. intro A.
       apply brel_set_intro_prop; auto. split. 
          intros s B.           
          apply in_minset_elim in B; auto. destruct B as [B C].
          apply in_minset_intro; auto. split. 
             apply in_set_bop_union_intro; auto. 
             intros t D.  apply in_set_bop_union_elim in D; auto. 
             destruct D as [D | D].
                apply C; auto.              
                destruct (A t D) as [x [E F]].                 
                case_eq(below lteS s t); intro G; auto. 
                   apply below_elim in G. destruct G as [G I].
                   assert (J := C x E). 
                   assert (K := lteTrans _ _ _ F G). 
                   apply below_false_elim in J. destruct J as [J | J].
                     rewrite K in J. discriminate J. 
                     assert (L := lteTrans _ _ _ J F). 
                     rewrite L in I.  discriminate I.                   
          
          intros s B. 
          apply in_minset_elim in B; auto. destruct B as [B C]. 
          apply in_set_bop_union_elim in B; auto. 
          destruct B as [B | B].
             apply in_minset_intro; auto. split; auto. 
             intros t D.              
             apply C. apply in_set_bop_union_intro; auto. 
          
             destruct (A s B) as [x [D E]].                              
             assert (F : x [in] (X [U] Y)). apply in_set_bop_union_intro; auto.
             assert (G := C x F).
             apply in_minset_intro; auto.  split; auto. 
                apply below_false_elim in G.
                destruct G as [G | G].
                   rewrite E in G. discriminate G. 
                   assert (I := anti _ _ G E). 
                   apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ I)); auto. 
                intros t H. 
                assert (I : t [in] (X [U] Y)). apply in_set_bop_union_intro; auto. 
                exact(C t I).
Qed. 

(* not used *) 
Lemma minset_lift_left_uop_invariant_weak
      (anti: brel_antisymmetric S rS lteS)      
      (RM : os_right_monotone lteS bS)  :
         ∀ X Y : finite_set S, ([ms] (([ms] X) [^] Y)) [=S] ([ms] (X [^] Y)).
Proof. intros X Y.
       apply brel_set_intro_prop; auto. split.
       + intros a A.
         apply in_minset_elim in A; auto. destruct A as [A B].
         apply in_minset_intro; auto. split. 
         * apply in_set_bop_lift_elim in A; auto.
           destruct A as [x [y [[C D] E]]]. 
           apply in_minset_elim in C; auto. destruct C as [C F].
           apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ E)).            
           apply in_set_bop_lift_intro; auto.            
         * intros t C. 
           apply in_set_bop_lift_elim in C; auto. 
           destruct C as [x [y [[D E] F]]].
           rewrite (below_congruence S rS lteS lteCong _ _ _ _ (refS a) F). 
           case_eq(in_set rS ([ms] X) x); intro G. 
           ** apply B.
              apply in_set_bop_lift_intro; auto.            
           ** apply in_set_minset_false_elim in G; auto.
              destruct G as [z [H I]].
              assert (J : (bS z y) [in] (([ms] X) [^] Y)). apply in_set_bop_lift_intro; auto.
              assert (K := B _ J).
              case_eq(below lteS a (bS x y)); intro L; auto. 
              *** apply below_elim in I. destruct I as [I1 I2]. 
                  assert (M := RM y z x I1). 
                  assert (N := below_pseudo_transitive_left _ _ lteTrans _ _ _ M L). 
                  rewrite N in K. discriminate K. 
       + intros a A. 
         apply in_minset_elim in A; auto. destruct A as [A B]. 
         apply in_set_bop_lift_elim in A; auto.
         destruct A as [x [y [[C D] E]]]. 
         apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ E)).            
         apply in_minset_intro; auto. split. 
         ++ apply in_set_bop_lift_intro; auto. 
            apply in_minset_intro; auto. split; auto. 
            +++ intros t F. 
                assert (G : (bS t y) [in] (X [^] Y)). apply in_set_bop_lift_intro; auto.
                assert (H := B _ G). 
                case_eq(below lteS x t); intro I; auto. 
                ++++ apply below_elim in I. destruct I as [I1 I2]. 
                     assert (J := RM y t x I1).
                     rewrite (below_congruence S rS lteS lteCong _ _ _ _ E (refS (bS t y))) in H.
                     apply below_false_elim in H. 
                     destruct H as [H | H].
                     +++++ rewrite J in H. discriminate H. 
                     +++++ assert (K := anti _ _ H J). 
                           admit. (*NEED STRICT MONO!!!*)
         ++ intros t F. 
            apply in_set_bop_lift_elim in F; auto. 
            destruct F as [u [v [[G H] I]]].             
            apply symS in E. 
            rewrite (below_congruence S rS lteS lteCong _ _ _ _ E (refS t)).
            apply B.
            apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ I)).
            apply in_minset_elim in G; auto. destruct G as [G _]. 
            apply in_set_bop_lift_intro; auto. 
Admitted.

(* not used *) 
Lemma minset_lift_right_uop_invariant_weak 
     : ∀ X Y : finite_set S, ([ms] (X [^] ([ms] Y))) [=S] ([ms] (X [^] Y)).
Admitted.


(* used in minset_union_lift_left_left_absorptive_strictly_increasing_weak *) 
Lemma lift_left_strictly_increasing 
      (sinc : os_left_strictly_increasing lteS bS) 
      (X Y : finite_set S):    
  (∀ (t : S), t [in] (X [^] Y) -> {x : S & (x [in] X) * (below lteS t x = true)}).
Proof. intros t A.   unfold os_left_strictly_increasing in sinc. 
       apply in_set_bop_lift_elim in A; auto. 
       destruct A as [x [y [[B C] D]]].
       exists x. split; auto. 
          rewrite (below_congruence _ _ _ lteCong _ _ _ _ D (refS x)).
          destruct (sinc x y) as [E F]. apply below_intro; auto. 
Qed.        

(* used in minset_union_lift_left_right_absorptive_strictly_increasing_weak *) 
Lemma lift_right_strictly_increasing 
      (sinc : os_right_strictly_increasing lteS bS) 
      (X Y : finite_set S):    
  (∀ (t : S), t [in] (Y [^] X) -> {x : S & (x [in] X) * (below lteS t x = true)}).
Proof. intros t A.   
       apply in_set_bop_lift_elim in A; auto. 
       destruct A as [x [y [[B C] D]]].
       exists y. split; auto.
          rewrite (below_congruence _ _ _ lteCong _ _ _ _ D (refS y)).       
          destruct (sinc y x) as [E F]. apply below_intro; auto. 
Qed.        

(* used in 
minset_union_lift_left_left_absorptive_strictly_increasing_weak 
minset_union_lift_left_right_absorptive_strictly_increasing_weak 
*) 
Lemma union_left_without_antisymmetry 
      (X Y : finite_set S):    
      (∀ (y : S), y [in] Y -> {x : S & (x [in] X) * (below lteS y x = true)})
      -> ([ms] X) [=S] ([ms] (X [U] Y)).
Proof. intro A.
       apply brel_set_intro_prop; auto. split. 
          intros s B.           
          apply in_minset_elim in B; auto. destruct B as [B C].
          apply in_minset_intro; auto. split. 
             apply in_set_bop_union_intro; auto. 
             intros t D.  apply in_set_bop_union_elim in D; auto. 
             destruct D as [D | D].
                apply C; auto.              
                destruct (A t D) as [x [E F]].                 
                case_eq(below lteS s t); intro G; auto. 
                   apply below_elim in G. destruct G as [G I].
                   assert (J := C x E). 
                   assert (K := below_pseudo_transitive_right S lteS lteTrans _ _ _ F G).
                   rewrite K in J. discriminate J.                    
          
          intros s B. 
          apply in_minset_elim in B; auto. destruct B as [B C]. 
          apply in_set_bop_union_elim in B; auto. 
          destruct B as [B | B].
             apply in_minset_intro; auto. split; auto. 
             intros t D.              
             apply C. apply in_set_bop_union_intro; auto. 
          
             destruct (A s B) as [x [D E]].                              
             assert (F : x [in] (X [U] Y)). apply in_set_bop_union_intro; auto. 
             assert (G := C x F).
             apply in_minset_intro; auto.  split; auto. 
                apply below_false_elim in G.
                destruct G as [G | G].  apply below_elim in E. destruct E as [E _]. 
                   rewrite E in G. discriminate G. 
                   assert (H := below_pseudo_transitive_left S lteS lteTrans _ _ _ G E).
                   rewrite below_not_reflexive in H; auto.  discriminate H. 
                intros t H. 
                assert (I : t [in] (X [U] Y)). apply in_set_bop_union_intro; auto. 
                exact(C t I).
Qed.


(***************** ID, ANN ********************************) 


Lemma minset_union_lift_exists_id_ann_equal :
      bops_exists_id_ann_equal (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS).
Proof. exists nil. split.
       apply bop_minset_union_id_is_nil; auto. 
       apply bop_minset_lift_ann_is_nil; auto.
Defined.

Lemma minset_lift_union_exists_id_ann_equal_partial_order_version  
      (LM : os_left_monotone lteS bS) 
      (RM : os_right_monotone lteS bS) 
      (anti : brel_antisymmetric S rS lteS)
      (bot_id : os_exists_bottom_id_equal rS lteS bS) :
      bops_exists_id_ann_equal (finite_set S) (brel_minset rS lteS) (bop_minset_lift S rS lteS bS) (bop_minset_union S rS lteS).
Proof. destruct bot_id as [bot [A B]]. 
       exists (bot :: nil). split.
       apply bop_minset_lift_id_is_bottom; auto.  (* here uses anitsymmetry, LM, and RM*) 
       apply bop_minset_union_exists_ann_is_bottom; auto. 
Defined.

Lemma minset_lift_union_exists_id_ann_equal_quasi_order_version   
   (LM : os_left_monotone lteS bS)
   (RM : os_right_monotone lteS bS)             
   (smono : os_left_strictly_monotone lteS bS * os_right_strictly_monotone lteS bS): 
   os_qo_exists_bottom_id_equal rS lteS bS ->   
       bops_exists_id_ann_equal (finite_set S) (brel_minset rS lteS) (bop_minset_lift S rS lteS bS) (bop_minset_union S rS lteS). 
Proof. intros [b [[A B] C]]. exists (b :: nil). split. 
       apply bop_minset_lift_id_is_bottom; auto. (* here uses smono, LM, and RM *)
       apply bop_minset_union_exists_ann_is_bottom; auto. 
Qed. 


(***************** Distributivity ********************************) 

(* why not make this an independent combinator? 
   it won't have absorption, but may be useful .... 
*) 
Lemma union_lift_left_distributive :
  bop_left_distributive (finite_set S) (brel_set rS) (bop_union rS) (bop_lift rS bS). 
Proof. intros X Y Z. 
       apply brel_set_intro_prop; auto.  split.
          intros a A.
          apply in_set_bop_lift_elim in A; auto. 
          destruct A as [b [c [[B C] D]]].
          apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ D)).          
          apply in_set_bop_union_elim in C; auto.
          apply in_set_bop_union_intro; auto. 
          destruct C as [C | C].
             left.  apply in_set_bop_lift_intro; auto.
             right.  apply in_set_bop_lift_intro; auto.
          
          intros a A. 
          apply in_set_bop_union_elim in A; auto. 
          destruct A as [A | A].
             apply in_set_bop_lift_elim in A; auto. 
             destruct A as [b [c [[B C] D]]].
             apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ D)).          
             apply in_set_bop_lift_intro; auto. 
             apply in_set_bop_union_intro; auto.

             apply in_set_bop_lift_elim in A; auto. 
             destruct A as [b [c [[B C] D]]].
             apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ D)).          
             apply in_set_bop_lift_intro; auto. 
             apply in_set_bop_union_intro; auto.
Qed.        




Lemma just_a_test : 
  bop_left_distributive (finite_set S) (brel_set rS) (bop_lift rS bS) (bop_union rS). 
Proof. intros X Y Z. 
       apply brel_set_intro_prop; auto.  split.
       ++ intros a A.
(*
  A : a [in] (X [U] (Y [^] Z))
  ============================
  a [in] ((X [U] Y) [^] (X [U] Z))

   a = x or a = yz -> a = xx or a = xz or x = yx or a = yz  Yes, if bS idempotent. 

*)          
          admit. 
       ++ intros a A.
(*
  A : a [in] ((X [U] Y) [^] (X [U] Z))
  ============================
  a [in] (X [U] (Y [^] Z))

Nope! 

But this may work with minset lift/union ??? 88


  A : a [in] ((X <U> Y) <^> (X <U> Z))
  ============================
  a [in] (X <U> (Y <^> Z))

Try this below. 

a = xx | xz | yx | yz 
-?-> 
a = x | yz

case a of 
| xx  -> OK by idem 
| xz  -> x in (X <U> Y)
         z in (X <U> Z)
         The difficult case: 
         x is y and z is x. 
| yx 
| yz -> OK 


*) 
Admitted.


(* Martelli 

A in min(subset, min(subset, X U Y) ^U min(subset, X U Z))
-> 
A in min(subset, X U min(subset, Y ^U Z))



A in min(subset, {x U y | x in min(subset, X U Y), y in min(subset, X U Z)})
-> 
A in min(subset, X U min(subset, {y U z | y in Y, z in Z }))

*) 

Lemma just_a_test_2 (X Y Z: finite_set S) (a : S) : 
  a [in] ((X <U> Y) <^> (X <U> Z)) -> a [in] (X <U> (Y <^> Z)).
Proof.  unfold bop_minset_lift, bop_minset_union.  intro A.
        apply in_minset_elim in A; auto.
        destruct A as [A D].
        apply in_set_bop_lift_elim in A; auto.
        destruct A as [x [y [[A B] C]]].
        apply in_minset_minset_elim in A; auto. 
        apply in_minset_minset_elim in B; auto.
        apply in_minset_intro; auto.        
        apply in_minset_elim in A; auto. destruct A as [A1 A2].
        apply in_minset_elim in B; auto. destruct B as [B1 B2].
        apply in_set_bop_union_elim in A1; auto.
        apply in_set_bop_union_elim in B1; auto.            
        destruct A1 as [A1 | A1]; destruct B1 as [B1 | B1]; split.
        + apply in_set_bop_union_intro; auto.
          left.
          rewrite (in_set_congruence _ _ symS tranS _ _ _ _ (set_reflexive ([ms] X)) C). 
          apply in_minset_intro; auto. split. 
          ++ (* think of martelli 
                X = set of sets 
                x in ms X iff x in X and no superset of x is in X 
                y in ms X iff y in X and no superset of y is in X 
                bS x y = x union y. 
              
              *)
            admit. 
          ++ intros t E. 
             case_eq(below lteS (bS x y) t); intro F; auto.              
             (*OK*) admit. 
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.           
 Admitted. 

Lemma union_lift_right_distributive :
  bop_right_distributive (finite_set S) (brel_set rS) (bop_union rS) (bop_lift rS bS). 
Proof. intros X Y Z. 
       apply brel_set_intro_prop; auto.  split.
          intros a A.
          apply in_set_bop_lift_elim in A; auto. 
          destruct A as [b [c [[B C] D]]].
          apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ D)).          
          apply in_set_bop_union_elim in B; auto.
          apply in_set_bop_union_intro; auto. 
          destruct B as [B | B].
             left.  apply in_set_bop_lift_intro; auto.
             right.  apply in_set_bop_lift_intro; auto.
          
          intros a A. 
          apply in_set_bop_union_elim in A; auto. 
          destruct A as [A | A].
             apply in_set_bop_lift_elim in A; auto. 
             destruct A as [b [c [[B C] D]]].
             apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ D)).          
             apply in_set_bop_lift_intro; auto. 
             apply in_set_bop_union_intro; auto.

             apply in_set_bop_lift_elim in A; auto. 
             destruct A as [b [c [[B C] D]]].
             apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ D)).          
             apply in_set_bop_lift_intro; auto. 
             apply in_set_bop_union_intro; auto.
Qed.        
              
Lemma minset_union_lift_left_distributive_weak
  (LM : os_left_monotone lteS bS)
  (RM : os_right_monotone lteS bS)       
  (DDD : (brel_antisymmetric S rS lteS) +  ((os_left_strictly_monotone lteS bS) * (os_right_strictly_monotone lteS bS))) : 
     bop_left_distributive (finite_set S) (brel_set rS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS). 
Proof. intros X Y Z.
       assert (A : (X <^> (Y <U> Z)) [=S] ([ms] (([ms] X) [^] ([ms] ([ms] (([ms] Y) [U] ([ms] Z))))))).
          unfold bop_minset_lift. unfold bop_minset_union. apply set_reflexive. 
       assert (B : ([ms] (([ms] X) [^] ([ms] ([ms] (([ms] Y) [U] ([ms] Z)))))) [=S] ([ms] (([ms] X) [^] ([ms] (([ms] Y) [U] ([ms] Z)))))).
          apply minset_lift_right_invariant_v0; auto.   (* uses DDD and LM ! *) 
       assert (C := set_transitive _ _ _ A B).          
       assert (D : ([ms] (([ms] X) [^] ([ms] (([ms] Y) [U] ([ms] Z))))) [=S] ([ms] (([ms] X) [^] (([ms] Y) [U] ([ms] Z))))). 
          apply minset_lift_right_invariant_v0; auto.
       assert (E := set_transitive _ _ _ C D).       
       assert (F := union_lift_left_distributive ([ms] X) ([ms] Y) ([ms] Z)).
       assert (G := uop_minset_congruence_weak _ _ F). 
       assert (H := set_transitive _ _ _ E G).       
       assert (I : ([ms] ((([ms] X) [^] ([ms] Y)) [U] (([ms] X) [^] ([ms] Z)))) [=S] ([ms] ((([ms] X) [^] ([ms] Y)) [U] ([ms] (([ms] X) [^] ([ms] Z)))))). 
          apply set_symmetric. apply minset_union_right_uop_invariant_weak. 
       assert (J := set_transitive _ _ _ H I).       
       assert (K : [ms] ((([ms] X) [^] ([ms] Y)) [U] ([ms] (([ms] X) [^] ([ms] Z))))
                     [=S] 
                   [ms] (([ms] (([ms] X) [^] ([ms] Y)))    [U] ([ms] ([ms] (([ms] X) [^] ([ms] Z)))))). 
          apply set_symmetric. apply minset_union_uop_invariant_weak. 
       assert (L := set_transitive _ _ _ J K).
       assert (M :  [ms] (([ms] (([ms] X) [^] ([ms] Y))) [U] ([ms] ([ms] (([ms] X) [^] ([ms] Z)))))
                       [=S] 
                    [ms] (([ms] ([ms] (([ms] X) [^] ([ms] Y)))) [U] ([ms] ([ms] (([ms] X) [^] ([ms] Z)))))).
       apply set_symmetric. apply minset_union_left_uop_invariant_weak. 
       assert (N := set_transitive _ _ _ L M).               
       assert (O : [ms] (([ms] ([ms] (([ms] X) [^] ([ms] Y)))) [U] ([ms] ([ms] (([ms] X) [^] ([ms] Z)))))
                      [=S]
                   ((X <^> Y) <U> (X <^> Z))).
          unfold bop_minset_lift. unfold bop_minset_union. apply set_reflexive. 
       exact (set_transitive _ _ _ N O).
Qed.


Lemma minset_union_lift_left_distributive
  (LM : os_left_monotone lteS bS)
  (RM : os_right_monotone lteS bS)             
  (DDD : (brel_antisymmetric S rS lteS) +  ((os_left_strictly_monotone lteS bS) * (os_right_strictly_monotone lteS bS))) :       
     bop_left_distributive (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS). 
Proof. intros X Y Z. apply set_equal_implies_minset_equal. apply minset_union_lift_left_distributive_weak; auto. Qed. 
       

Lemma minset_union_lift_right_distributive_weak
  (LM : os_left_monotone lteS bS)      
  (RM : os_right_monotone lteS bS)
  (DDD : (brel_antisymmetric S rS lteS) +  ((os_left_strictly_monotone lteS bS) * (os_right_strictly_monotone lteS bS))) :       
     bop_right_distributive (finite_set S) (brel_set rS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS). 
Proof. intros X Y Z. unfold bop_minset_lift. unfold bop_minset_union.
       assert (A : ((Y <U> Z) <^> X ) [=S] ([ms] (([ms] ([ms] (([ms] Y) [U] ([ms] Z)))) [^] ([ms] X)))). 
          unfold bop_minset_lift. unfold bop_minset_union. apply set_reflexive. 
       assert (B : ([ms] (([ms] ([ms] (([ms] Y) [U] ([ms] Z)))) [^] ([ms] X)))
                        [=S]
                   ([ms] ((([ms] (([ms] Y) [U] ([ms] Z)))) [^] ([ms] X)))).
          apply minset_lift_left_invariant_v0; auto. (* uses DDD and RM *) 
       assert (C := set_transitive _ _ _ A B).  
       assert (D : [ms] ((([ms] (([ms] Y) [U] ([ms] Z)))) [^] ([ms] X))
                     [=S]
                   [ms] ((([ms] Y) [U] ([ms] Z)) [^] ([ms] X))).
          apply minset_lift_left_invariant_v0; auto.
       assert (E := set_transitive _ _ _ C D).       
       assert (F := union_lift_right_distributive ([ms] X) ([ms] Y) ([ms] Z)).
       assert (G := uop_minset_congruence_weak _ _ F). 
       assert (H := set_transitive _ _ _ E G).       
       assert (I : ([ms] ((([ms] Y) [^] ([ms] X)) [U] (([ms] Z) [^] ([ms] X))))
                     [=S]
                   ([ms] ( ([ms] (([ms] Y) [^] ([ms] X))) [U] (([ms] Z) [^] ([ms] X))))).
          apply set_symmetric. apply minset_union_left_uop_invariant_weak. 
       assert (J := set_transitive _ _ _ H I).       
       assert (K : ([ms] ( ([ms] (([ms] Y) [^] ([ms] X))) [U] (([ms] Z) [^] ([ms] X))))
                     [=S] 
                   ([ms] (([ms] ([ms] (([ms] Y) [^] ([ms] X)))) [U] ([ms] (([ms] Z) [^] ([ms] X)))))). 
          apply set_symmetric. apply minset_union_uop_invariant_weak. 
       assert (L := set_transitive _ _ _ J K).
       assert (M :  [ms] (([ms] ([ms] (([ms] Y) [^] ([ms] X)))) [U] ([ms] (([ms] Z) [^] ([ms] X))))
                       [=S] 
                    [ms] (([ms] ([ms] (([ms] Y) [^] ([ms] X)))) [U] ([ms] ([ms] (([ms] Z) [^] ([ms] X)))))).
       apply set_symmetric. apply minset_union_right_uop_invariant_weak. 
       assert (N := set_transitive _ _ _ L M).               
       assert (O : [ms] (([ms] ([ms] (([ms] Y) [^] ([ms] X)))) [U] ([ms] ([ms] (([ms] Z) [^] ([ms] X)))))
                      [=S]
                   ((Y <^> X) <U> (Z <^> X))).
          unfold bop_minset_lift. unfold bop_minset_union. apply set_reflexive. 
       exact (set_transitive _ _ _ N O).
Qed.


Lemma minset_union_lift_right_distributive
  (LM : os_left_monotone lteS bS)            
  (RM : os_right_monotone lteS bS)      
  (DDD : (brel_antisymmetric S rS lteS) +  ((os_left_strictly_monotone lteS bS) * (os_right_strictly_monotone lteS bS))) :   
     bop_right_distributive (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS). 
Proof. intros X Y Z. apply set_equal_implies_minset_equal. apply minset_union_lift_right_distributive_weak; auto. Qed. 



(********************** ABSORPTION ***************************)

Lemma minset_union_lift_left_left_absorptive_increasing_weak
      (anti: brel_antisymmetric S rS lteS)
      (inc : os_left_increasing lteS bS)       
      (X Y : finite_set S):    
      ([ms] X) [=S] ([ms] (X [U] (X [^] Y))).
Proof.  apply  union_left_antisymmetric; auto. apply lift_left_increasing; auto. Qed. 

Lemma minset_union_lift_left_right_absorptive_increasing_weak
      (anti: brel_antisymmetric S rS lteS)
      (inc : os_right_increasing lteS bS)       
      (X Y : finite_set S):    
      ([ms] X) [=S] ([ms] (X [U] (Y [^] X))).
Proof.  apply  union_left_antisymmetric; auto. apply lift_right_increasing; auto. Qed.


(* 

Lemma minset_union_lift_left_left_absorptive    !!!!!!!!!!!!!!!!!!!
      (anti : brel_antisymmetric S rS lteS)
      (LM : os_left_monotone lteS bS) 
      (RM : os_right_monotone lteS bS) 
      (bot_id : os_bottom_equals_id rS lteS bS) :
     bops_left_left_absorptive (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS). 
Proof. apply id_ann_implies_left_left_absorptive.
       apply minset_reflexive. 
       apply minset_transitive. 
       apply minset_symmetric. 
       apply bop_minset_union_congruence; auto. 
       apply bop_minset_lift_congruence; auto. 
       apply minset_union_lift_left_distributive; auto. 
       apply minset_union_lift_ann_equals_id; auto. 
Qed. 



Lemma minset_union_lift_left_right_absorptive   !!!!!!!!!!!!!!!!!!!!!!
      (anti : brel_antisymmetric S rS lteS)
      (LM : os_left_monotone lteS bS) 
      (RM : os_right_monotone lteS bS) 
      (bot_id : os_bottom_equals_id rS lteS bS) :
     bops_left_right_absorptive (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS). 
Proof. apply id_ann_implies_left_right_absorptive.
       apply minset_reflexive. 
       apply minset_transitive. 
       apply minset_symmetric. 
       apply bop_minset_union_congruence; auto.
       apply bop_minset_union_commutative; auto.        
       apply bop_minset_lift_congruence; auto. 
       apply minset_union_lift_right_distributive; auto. 
       apply minset_union_lift_ann_equals_id; auto. 
Qed. 

*) 
       
(* STRICT VERSIONS *)

Lemma minset_union_lift_left_left_absorptive_strictly_increasing_weak
      (sinc : os_left_strictly_increasing lteS bS)       
      (X Y : finite_set S):    
        ([ms] X) [=S] ([ms] (X [U] (X [^] Y))).
Proof.  apply  union_left_without_antisymmetry; auto. apply lift_left_strictly_increasing; auto. Qed.       

Lemma minset_union_lift_left_right_absorptive_strictly_increasing_weak
      (sinc : os_right_strictly_increasing lteS bS)       
      (X Y : finite_set S):    
      ([ms] X) [=S] ([ms] (X [U] (Y [^] X))).
Proof.  apply  union_left_without_antisymmetry; auto. apply lift_right_strictly_increasing; auto. Qed. 



(*   X [=MS] (X <U> (X <^> Y))  *) 
Lemma minset_union_lift_left_left_absorptive_increasing
      (anti: brel_antisymmetric S rS lteS)
      (inc : os_left_increasing lteS bS) :
  bops_left_left_absorptive (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS).
Proof. intros X Y.
       unfold brel_minset. unfold bop_minset_union. unfold bop_minset_lift. 
       assert (A := uop_minset_idempotent X).  apply set_symmetric in A.
       assert (B : ([ms] ([ms] X)) [=S] ([ms] (([ms] X) [U] (([ms] X) [^] ([ms] Y))))).
          apply minset_union_lift_left_left_absorptive_increasing_weak; auto. 
       assert (C := set_transitive _ _ _ A B). 
       assert (D : [ms] (([ms] X) [U] (([ms] X) [^] ([ms] Y)))
                         [=S]
                   [ms] (([ms] X) [U] ([ms] (([ms] X) [^] ([ms] Y))))).           
          apply set_symmetric. apply minset_union_right_uop_invariant_weak; auto. 
       assert (E := set_transitive _ _ _ C D).
       assert (F : [ms] (([ms] X) [U] ([ms] (([ms] X) [^] ([ms] Y))))
                        [=S] 
                  [ms] (([ms] X) [U] ([ms] ([ms] (([ms] X) [^] ([ms] Y)))))). 
          apply set_symmetric. apply minset_union_right_uop_invariant_weak; auto.
       assert (G := set_transitive _ _ _ E F).       
       assert (H := uop_minset_idempotent (([ms] X) [U] ([ms] ([ms] (([ms] X) [^] ([ms] Y)))))).
       apply set_symmetric in H. exact (set_transitive _ _ _ G H). 
Qed.

(*  X [=MS] (X <U> (Y <^> X))  *) 
Lemma minset_union_lift_left_right_absorptive_increasing 
  (anti: brel_antisymmetric S rS lteS)
  (inc : os_right_increasing lteS bS) :
     bops_left_right_absorptive (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS).
Proof. intros X Y.     
       unfold brel_minset. unfold bop_minset_union. unfold bop_minset_lift. 
       assert (A := uop_minset_idempotent X).  apply set_symmetric in A.
       assert (B : ([ms] ([ms] X)) [=S] ([ms] (([ms] X) [U] (([ms] Y) [^] ([ms] X))))).
          apply minset_union_lift_left_right_absorptive_increasing_weak; auto. 
       assert (C := set_transitive _ _ _ A B). 
       assert (D : [ms] (([ms] X) [U] (([ms] Y) [^] ([ms] X)))
                         [=S]
                   [ms] (([ms] X) [U] ([ms] (([ms] Y) [^] ([ms] X))))).           
          apply set_symmetric. apply minset_union_right_uop_invariant_weak; auto. 
       assert (E := set_transitive _ _ _ C D).
       assert (F : [ms] (([ms] X) [U] ([ms] (([ms] Y) [^] ([ms] X))))
                        [=S] 
                  [ms] (([ms] X) [U] ([ms] ([ms] (([ms] Y) [^] ([ms] X)))))). 
          apply set_symmetric. apply minset_union_right_uop_invariant_weak; auto.
       assert (G := set_transitive _ _ _ E F).       
       assert (H := uop_minset_idempotent (([ms] X) [U] ([ms] ([ms] (([ms] Y) [^] ([ms] X)))))).
       apply set_symmetric in H. exact (set_transitive _ _ _ G H). 
Qed.



(*   X [=MS] (X <U> (X <^> Y))  *) 
Lemma minset_union_lift_left_left_absorptive_strictly_increasing
      (sinc : os_left_strictly_increasing lteS bS) :
  bops_left_left_absorptive (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS).
Proof. intros X Y.
       unfold brel_minset. unfold bop_minset_union. unfold bop_minset_lift. 
       assert (A := uop_minset_idempotent X).  apply set_symmetric in A.
       assert (B : ([ms] ([ms] X)) [=S] ([ms] (([ms] X) [U] (([ms] X) [^] ([ms] Y))))).
          apply minset_union_lift_left_left_absorptive_strictly_increasing_weak; auto. 
       assert (C := set_transitive _ _ _ A B). 
       assert (D : [ms] (([ms] X) [U] (([ms] X) [^] ([ms] Y)))
                         [=S]
                   [ms] (([ms] X) [U] ([ms] (([ms] X) [^] ([ms] Y))))).           
          apply set_symmetric. apply minset_union_right_uop_invariant_weak; auto. 
       assert (E := set_transitive _ _ _ C D).
       assert (F : [ms] (([ms] X) [U] ([ms] (([ms] X) [^] ([ms] Y))))
                        [=S] 
                  [ms] (([ms] X) [U] ([ms] ([ms] (([ms] X) [^] ([ms] Y)))))). 
          apply set_symmetric. apply minset_union_right_uop_invariant_weak; auto.
       assert (G := set_transitive _ _ _ E F).       
       assert (H := uop_minset_idempotent (([ms] X) [U] ([ms] ([ms] (([ms] X) [^] ([ms] Y)))))).
       apply set_symmetric in H. exact (set_transitive _ _ _ G H). 
Qed.

(*  X [=MS] (X <U> (Y <^> X))  *) 
Lemma minset_union_lift_left_right_absorptive_strictly_increasing 
  (sinc : os_right_strictly_increasing lteS bS) :
     bops_left_right_absorptive (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS).
Proof. intros X Y.     
       unfold brel_minset. unfold bop_minset_union. unfold bop_minset_lift. 
       assert (A := uop_minset_idempotent X).  apply set_symmetric in A.
       assert (B : ([ms] ([ms] X)) [=S] ([ms] (([ms] X) [U] (([ms] Y) [^] ([ms] X))))).
          apply minset_union_lift_left_right_absorptive_strictly_increasing_weak; auto. 
       assert (C := set_transitive _ _ _ A B). 
       assert (D : [ms] (([ms] X) [U] (([ms] Y) [^] ([ms] X)))
                         [=S]
                   [ms] (([ms] X) [U] ([ms] (([ms] Y) [^] ([ms] X))))).           
          apply set_symmetric. apply minset_union_right_uop_invariant_weak; auto. 
       assert (E := set_transitive _ _ _ C D).
       assert (F : [ms] (([ms] X) [U] ([ms] (([ms] Y) [^] ([ms] X))))
                        [=S] 
                  [ms] (([ms] X) [U] ([ms] ([ms] (([ms] Y) [^] ([ms] X)))))). 
          apply set_symmetric. apply minset_union_right_uop_invariant_weak; auto.
       assert (G := set_transitive _ _ _ E F).       
       assert (H := uop_minset_idempotent (([ms] X) [U] ([ms] ([ms] (([ms] Y) [^] ([ms] X)))))).
       apply set_symmetric in H. exact (set_transitive _ _ _ G H). 
Qed.

End Theory.


Section ACAS.

Section Decide.
End Decide.

Section Proofs.
End Proofs.

Section Combinators. 
End Combinators.   

(* 
For distributivity need 

  (LM : os_left_monotone lteS bS)
  (RM : os_right_monotone lteS bS)       
  (DDD : (brel_antisymmetric S rS lteS) +  ((os_left_strictly_monotone lteS bS) * (os_right_strictly_monotone lteS bS))) : 

absorption 

      (anti: brel_antisymmetric S rS lteS)
      (inc : os_left_increasing lteS bS)       
      (inc : os_right_increasing lteS bS)       

id_ann? 

*)   

End ACAS. 

(*



Definition minset_union_lift_bottom_with_one_proofs_to_with_one_proofs
           (S: Type) (eq lte : brel S) (times : binary_op S)             
           (P  : bottom_with_one_proofs S eq lte times) :
  with_one_proofs (finite_set S) (brel_minset S eq lte) (bop_minset_union S eq lte) (bop_minset_lift S eq lte times) :=  
let top_d     := A_bottom_with_one_exists_top_d _ _ _ _ P in 
let bot       := A_bottom_with_one_exists_bottom _ _ _ _ P in 
let one       := A_bottom_with_one_exists_times _ _ _ _ P in 
let ann_d     := A_bottom_with_one_exists_times_ann_d _ _ _ _ P in 
let top_ann_d := A_bottom_with_one_top_ann_d _ _ _ _ P in 
let bot_one   := A_bottom_with_one_bottom_one _ _ _ _ P in 
{|
  A_with_one_exists_plus_id_d          := inl (bop_minset_union_exists_id S eq ref sym trn lte lteCng lteRef lteTrn) 
; A_with_one_exists_plus_ann           := bop_exists_ann S eq plus
; A_with_one_exists_times_id           := bop_exists_id S eq times
; A_with_one_exists_times_ann_d        := inl (bop_minset_union_exists_ann_with_antisymmetry S eq ref sym trn lte lteCng lteTrn anti bot) 
; A_with_one_plus_id_is_times_ann_d    := inr (minset_union_lift_not_id_equals_ann) 
; A_with_one_times_id_is_plus_ann      := minset_union_lift_ann_equals_id S eq ref sym trn lte lteCng lteRef lteTrn times timesCng LM RM anit bot_one 
|}.
r



(*  
Record A_monotone_posg (S : Type) := {
  A_mposg_eqv          : A_eqv S 
; A_mposg_lte          : brel S 
; A_mposg_times        : binary_op S 
; A_mposg_lte_proofs   : po_proofs S (A_eqv_eq S A_mposg_eqv) A_mposg_lte
; A_mposg_times_proofs : msg_proofs S (A_eqv_eq S A_mposg_eqv) A_mposg_times
; A_mposg_top_bottom   : top_bottom_ann_id_with_id_proofs S (A_eqv_eq S A_mposg_eqv) A_mposg_lte A_mposg_times                                    
; A_mposg_proofs       : monotone_os_proofs S A_mposg_lte A_mposg_times 
; A_mposg_ast          : cas_ast
}.

Record A_pre_path_algebra_with_one (S : Type) := {
  A_pre_path_algebra_with_one_eqv           : A_eqv S 
; A_pre_path_algebra_with_one_plus          : binary_op S 
; A_pre_path_algebra_with_one_times         : binary_op S 
; A_pre_path_algebra_with_one_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_pre_path_algebra_with_one_eqv) A_pre_path_algebra_with_one_plus
; A_pre_path_algebra_with_one_times_proofs  : msg_proofs S   (A_eqv_eq S A_pre_path_algebra_with_one_eqv) A_pre_path_algebra_with_one_times
; A_pre_path_algebra_with_one_id_ann_proofs : with_one_proofs S (A_eqv_eq S A_pre_path_algebra_with_one_eqv) A_pre_path_algebra_with_one_plus A_pre_path_algebra_with_one_times
; A_pre_path_algebra_with_one_proofs        : path_algebra_proofs S (A_eqv_eq S A_pre_path_algebra_with_one_eqv) A_pre_path_algebra_with_one_plus A_pre_path_algebra_with_one_times
; A_pre_path_algebra_with_one_ast           : cas_ast
}.




Record path_algebra_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_path_algebra_left_distributive      : bop_left_distributive S eq plus times 
; A_path_algebra_right_distributive     : bop_right_distributive S eq plus times 
; A_path_algebra_left_left_absorptive   : bops_left_left_absorptive S eq plus times 
; A_path_algebra_left_right_absorptive  : bops_left_right_absorptive S eq plus times 
}.




sg_CI_proofs_minset_union_from_po
     : ∀ (S : Type) (rS lteS : brel S),
         S
         → ∀ f : S → S,
             brel_not_trivial S rS f
             → eqv_proofs S rS
               → po_proofs S rS lteS
                 → sg_CI_proofs (finite_set S) (brel_minset rS lteS)
                     (bop_minset_union S rS lteS)

A_minset_lift_monotone_os_proofs_to_msg_proofs
     : ∀ (S : Type) (eq lte : brel S) (b : binary_op S),
         eqv_proofs S eq
         → S
           → ∀ f : S → S,
               brel_not_trivial S eq f
               → bop_exists_id S eq b
                 → po_proofs S eq lte
                   → msg_proofs S eq b
                     → monotone_os_proofs S lte b
                       → msg_proofs (finite_set S) 
                           (brel_minset eq lte) (bop_minset_lift S eq lte b)

*) 





End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.     
*) 
