Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.theory.set.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.union.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.cast_up. 
Require Import CAS.coq.po.theory.
Require Import CAS.coq.po.subset.
Require Import CAS.coq.po.minset_subset.
Require Import CAS.coq.po.dual.
Require Import CAS.coq.po.from_sg. 

Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures. 
Require Import CAS.coq.os.theory. 



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


(* NB: antisymmetry is not assumed! *) 
Variable lteS : brel S.
Variable lteCong : brel_congruence S rS lteS.
Variable lteRefl : brel_reflexive S lteS.
Variable lteTrans : brel_transitive S lteS. 



Definition bop_minset_union : binary_op (finite_set S)
  := λ X Y, uop_minset lteS (bop_union rS (uop_minset lteS X) (uop_minset lteS Y)). 



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
Notation "a <U> b" := (bop_minset_union a b)         (at level 15).

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
Definition bop_union_congruence := bop_union_congruence _ _ refS symS tranS.
Definition bop_union_idempotent := bop_union_idempotent _ _ refS symS tranS.
Definition bop_union_commutative := bop_union_commutative _ _ refS symS tranS.
Definition bop_union_associative := bop_union_associative _ _ refS symS tranS.
Definition set_equal_implies_minset_equal := set_equal_implies_minset_equal S rS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition brel_minset_transitive := brel_minset_transitive S rS refS symS tranS lteS.
Definition uop_minset_is_antichain := uop_minset_is_antichain S rS refS symS lteS lteCong lteRefl.
Definition fundamental_minset_theorem := fundamental_minset_theorem S rS refS symS tranS lteS lteCong lteTrans.


Lemma bop_minset_union_congruence_weak : bop_congruence (finite_set S) (brel_set rS) bop_minset_union.
Proof. unfold bop_congruence. intros X1 X2 Y1 Y2 A B.
       unfold bop_minset_union.
       assert (C := uop_minset_congruence_weak _ _ A).
       assert (D := uop_minset_congruence_weak _ _ B).       
       assert (E := bop_union_congruence _ _ _ _ C D).
       apply set_equal_implies_minset_equal; auto. 
Qed. 

Lemma bop_minset_union_congruence : bop_congruence (finite_set S) (brel_minset rS lteS) bop_minset_union.
Proof. unfold bop_congruence. intros X1 X2 Y1 Y2 A B.
       unfold bop_minset_union.
       unfold brel_minset in A, B. 
       assert (C := bop_union_congruence _ _ _ _ A B).
       assert (D := uop_minset_congruence_weak _ _ C).
       unfold brel_minset. 
       apply uop_minset_congruence_weak; auto. 
Qed.

Lemma minset_union_commutative_weak (X Y : finite_set S) : ([ms] (X [U] Y)) [=S] ([ms] (Y [U] X)). 
Proof. assert (A : (X [U] Y) [=S] (Y [U] X)).
          apply bop_union_commutative; auto. 
       exact (uop_minset_congruence_weak _ _ A).
Qed. 


Lemma bop_minset_union_commutative : bop_commutative (finite_set S) (brel_minset rS lteS) bop_minset_union.
Proof. intros X Y.
       unfold bop_minset_union.
       assert (A := minset_union_commutative_weak ([ms] X) ([ms] Y)).
       apply set_equal_implies_minset_equal; auto. 
Qed. 


Lemma minset_union_left_uop_invariant_weak (X Y : finite_set S): [ms] (([ms] X) [U] Y) [=S] [ms] (X [U] Y). 
Proof.   apply brel_set_intro_prop; auto. split. 
            intros s A. 
            apply in_minset_elim in A; auto. destruct A as [A B]. 
            apply in_set_bop_union_elim in A; auto.             
            destruct A as [A | A].
               apply in_minset_elim in A; auto. destruct A as [A C]. 
               apply in_minset_intro; auto. split. 
                  apply in_set_bop_union_intro; auto. 
                  intros t D. 
                  apply in_set_bop_union_elim in D; auto. 
                  destruct D as [D | D].
                     apply C; auto. 
                     apply B; auto. 
                     apply in_set_bop_union_intro; auto.                         
               apply in_minset_intro; auto. split. 
                  apply in_set_bop_union_intro; auto. 
                  intros t C.
                  apply in_set_bop_union_elim in C; auto. 
                  destruct C as [C | C]. 
                     case_eq(in_set rS ([ms] X) t); intro D. 
                        apply B; auto.                      
                        apply in_set_bop_union_intro; auto.                         
                        apply in_set_minset_false_elim in D; auto. 
                        destruct D as [u [D E]]. 
                        assert (F : u [in] (([ms] X) [U] Y)).
                           apply in_set_bop_union_intro; auto. 
                        assert (G := B _ F).
                        case_eq(below lteS s t);intro H; auto. 
                           assert (I := below_transitive _ _ lteTrans _ _ _ E H). 
                           rewrite I in G. discriminate G.                            
                     apply B; auto.                      
                     apply in_set_bop_union_intro; auto. 

            intros s A. 
            apply in_minset_elim in A; auto. destruct A as [A B].
            apply in_minset_intro; auto. split. 
               apply in_set_bop_union_intro; auto. 
               apply in_set_bop_union_elim in A; auto.
               destruct A as [A| A].
                  left. apply in_minset_intro; auto. split; auto. 
                     intros t C. apply B. 
                     apply in_set_bop_union_intro; auto. 
                  right; auto. 
               intros t C.
               apply in_set_bop_union_elim in C; auto. 
               destruct C as [C | C].                
                  apply B. apply in_minset_elim in C; auto.
                  destruct C as [C _].
                  apply in_set_bop_union_intro; auto.                   
                  apply B. apply in_set_bop_union_intro; auto.
Qed. 
                                                                         
Lemma minset_union_left_uop_invariant (X Y : finite_set S): [ms] (([ms] X) [U] Y) [=MS] [ms] (X [U] Y). 
Proof. assert (A := minset_union_left_uop_invariant_weak X Y).  apply set_equal_implies_minset_equal; auto. Qed.

Lemma minset_union_right_uop_invariant_weak (X Y : finite_set S): [ms] (X [U] ([ms] Y)) [=S] [ms] (X [U] Y). 
Proof. assert (A := bop_union_commutative X ([ms] Y)). 
       assert (B := uop_minset_congruence_weak _ _ A).
       assert (C :=  minset_union_left_uop_invariant_weak Y X).
       assert (D := set_transitive _ _ _ B C).
       assert (E := bop_union_commutative Y X).
       assert (F := uop_minset_congruence_weak _ _ E).       
       exact (set_transitive _ _ _ D F).
Qed. 

Lemma minset_union_right_uop_invariant (X Y : finite_set S): [ms] (X [U] ([ms] Y)) [=MS] [ms] (X [U] Y). 
Proof. assert (A := minset_union_right_uop_invariant_weak X Y).  apply set_equal_implies_minset_equal; auto. Qed.

Lemma minset_union_uop_invariant_weak (X Y : finite_set S): [ms] (([ms] X) [U] ([ms] Y)) [=S] [ms] (X [U] Y). 
Proof.  assert (A : [ms] (([ms] X) [U] ([ms] Y)) [=S] [ms] (X [U] ([ms] Y))).
           apply minset_union_left_uop_invariant_weak. 
        assert (B : [ms] (X [U] ([ms] Y)) [=S] [ms] (X [U] Y)).
           apply minset_union_right_uop_invariant_weak.
        exact (set_transitive _ _ _ A B).
Qed.

Lemma fundamental_minset_union_theorem (X Y : finite_set S) :
       {Z : finite_set S &
            ((X [U] Y) [=S] ((X <U> Y) [U] Z)) *
            (∀ s : S, s [in] Z → {t : S & t [in] (X <U> Y) * t << s})
       }. 
Proof. assert (A := fundamental_minset_theorem (X [U] Y)).
       destruct A as [Z [B C]]. 
       assert (D := minset_union_uop_invariant_weak X Y).
       exists Z. split.
       + apply set_symmetric in D.
         assert (E := bop_union_congruence _ _ _ _ D (set_reflexive Z)). 
         assert (F := set_transitive _ _ _ B E).
         unfold bop_minset_union.
         exact F. 
       + intros s E. 
         destruct (C s E) as [t [F G]].
         exists t. split; auto. 
         unfold bop_minset_union.
         rewrite (in_set_congruence _ _ symS tranS _ _ _ _ D (refS t)).
         exact F. 
Defined. 



Lemma minset_union_uop_invariant (X Y : finite_set S): [ms] (([ms] X) [U] ([ms] Y)) [=MS] [ms] (X [U] Y). 
Proof. assert (A := minset_union_uop_invariant_weak X Y).  apply set_equal_implies_minset_equal; auto. Qed.

Lemma bop_minset_union_associative : bop_associative (finite_set S) (brel_minset rS lteS)  (bop_minset_union).
Proof. intros X Y Z.
       assert (A : ((X <U> Y) <U> Z) [=MS] [ms] (([ms] (X <U> Y)) [U] ([ms] Z))).
           apply brel_minset_reflexive; auto. 
       assert (B : [ms] (([ms] (X <U> Y)) [U] ([ms] Z)) [=MS]  [ms] ((X <U> Y) [U] ([ms] Z))). 
           apply minset_union_left_uop_invariant. 
       assert (C : ((X <U> Y) <U> Z) [=MS] [ms] ((X <U> Y) [U] ([ms] Z))). 
          exact (minset_transitive _ _ _ A B).
       assert (D : [ms] ((X <U> Y) [U] ([ms] Z))  [=MS] [ms] ([ms] (([ms] X) [U] ([ms] Y)) [U] ([ms] Z))). 
           apply brel_minset_reflexive; auto. 
       assert (E : ((X <U> Y) <U> Z) [=MS] [ms] ([ms] (([ms] X) [U] ([ms] Y)) [U] ([ms] Z))). 
          exact (minset_transitive _ _ _ C D).
       assert (F : [ms] ([ms] (([ms] X) [U] ([ms] Y)) [U] ([ms] Z)) [=MS] [ms] ((([ms] X) [U] ([ms] Y)) [U] ([ms] Z))).
           apply minset_union_left_uop_invariant.            
       assert (G : ((X <U> Y) <U> Z) [=MS] [ms] ((([ms] X) [U] ([ms] Y)) [U] ([ms] Z))).
          exact(minset_transitive _ _ _ E F).
       assert (H : [ms] ((([ms] X) [U] ([ms] Y)) [U] ([ms] Z)) [=MS] [ms] (([ms] X) [U] (([ms] Y) [U] ([ms] Z)))). 
          assert (AS := bop_union_associative ([ms] X) ([ms] Y) ([ms] Z)).
          apply set_equal_implies_minset_equal in AS. 
          apply uop_minset_congruence; auto. 
       assert (I : ((X <U> Y) <U> Z) [=MS] [ms] (([ms] X) [U] (([ms] Y) [U] ([ms] Z)))).
          exact(minset_transitive _ _ _  G H).          
       assert (J : [ms] (([ms] X) [U] (([ms] Y) [U] ([ms] Z))) [=MS] [ms] (([ms] X) [U] ([ms] (([ms] Y) [U] ([ms] Z))))).
           apply brel_minset_symmetric. 
           apply minset_union_right_uop_invariant. 
       assert (K : ((X <U> Y) <U> Z) [=MS] [ms] (([ms] X) [U] ([ms] (([ms] Y) [U] ([ms] Z))))).
          exact(minset_transitive _ _ _  I J).
       assert (L : [ms] (([ms] X) [U] ([ms] (([ms] Y) [U] ([ms] Z)))) [=MS] [ms] (([ms] X) [U] (Y <U> Z))).
          apply brel_minset_reflexive; auto. 
       assert (M : ((X <U> Y) <U> Z) [=MS] [ms] (([ms] X) [U] (Y <U> Z))).
          exact(minset_transitive _ _ _  K L).
       assert (N : [ms] (([ms] X) [U] (Y <U> Z)) [=MS] [ms] (([ms] X) [U] ([ms] (Y <U> Z)))).
           apply brel_minset_symmetric. 
           apply minset_union_right_uop_invariant. 
       assert (O : ((X <U> Y) <U> Z) [=MS] [ms] (([ms] X) [U] ([ms] (Y <U> Z)))).
          exact(minset_transitive _ _ _  M N).
       assert (P : [ms] (([ms] X) [U] ([ms] (Y <U> Z))) [=MS] (X <U> (Y <U> Z))). 
          apply brel_minset_reflexive; auto. 
       exact(minset_transitive _ _ _  O P).
Qed. 

Lemma bop_minset_union_idempotent : bop_idempotent (finite_set S) (brel_minset rS lteS) bop_minset_union.
Proof. intro X. 
       unfold bop_minset_union.
       unfold brel_minset.
       assert (A := uop_minset_idempotent (([ms] X) [U] ([ms] X))). 
       assert (B := bop_union_idempotent ([ms] X)).
       apply uop_minset_congruence_weak in B; auto.
       assert (C := set_transitive _ _ _ A B). 
       assert (D := uop_minset_idempotent X). 
       exact (set_transitive _ _ _ C D). 
Qed.


Lemma bop_minset_union_nil_left (X : finite_set S) :  (nil <U> X) [=MS] X. 
Proof. unfold bop_minset_union. unfold brel_minset.        
       rewrite minset_empty.
       assert (A := bop_union_with_nil_left S rS refS symS tranS ([ms] X)).
       apply uop_minset_congruence_weak in A.
       assert (B := uop_minset_idempotent ((nil [U] ([ms] X)))).               
       assert (C := uop_minset_idempotent X).
       exact (set_transitive _ _ _ B (set_transitive _ _ _ A C)). 
Qed.


Lemma bop_minset_union_nil_right (X : finite_set S) : (X <U> nil) [=MS] X.
Proof. assert (A := bop_minset_union_nil_left X). 
       assert (B := bop_minset_union_commutative nil X). 
       apply minset_symmetric in B.
       exact (minset_transitive _ _ _ B A).  
Qed.

Lemma bop_minset_union_id_is_nil : bop_is_id (finite_set S) (brel_minset rS lteS) bop_minset_union nil. 
Proof. split. 
         apply bop_minset_union_nil_left. 
         apply bop_minset_union_nil_right.
Qed.

Lemma bop_minset_union_exists_id : bop_exists_id (finite_set S) (brel_minset rS lteS) bop_minset_union. 
Proof. exists nil. apply bop_minset_union_id_is_nil. Defined.


(* next two should be in union.v *) 

Lemma bop_union_cons_shift (X : finite_set S) (s : S) : ((s :: nil) [U] X)  [=S] (s :: X).
Proof. apply brel_set_intro_prop; auto. split. 
          intros t A. apply in_set_bop_union_elim in A; auto.
          apply in_set_cons_intro; auto.
          destruct A as [A | A].
             apply in_set_singleton_elim in A; auto. 
             right; auto.           
          intros t A. apply in_set_bop_union_intro; auto.
          apply in_set_cons_elim in A; auto.
          destruct A as [A | A].
             left. apply in_set_singleton_intro; auto. 
             right; auto.           
Qed.           

Lemma bop_union_cons_shift_v2 (X : finite_set S) (s : S) : (X [U] (s :: nil) )  [=S] (s :: X).
Proof. apply brel_set_intro_prop; auto. split. 
          intros t A. apply in_set_bop_union_elim in A; auto.
          apply in_set_cons_intro; auto.
          destruct A as [A | A].
             right; auto.           
             apply in_set_singleton_elim in A; auto. 
          intros t A. apply in_set_bop_union_intro; auto.
          apply in_set_cons_elim in A; auto.
          destruct A as [A | A].
             right. apply in_set_singleton_intro; auto. 
             left; auto. 
Qed.           

(********************** BOTTOM ***********************

Note : proofs that expose iterate_minset should be 
moved to eqv/minset.v ....

*******)


Lemma iterate_minset_bottom  (b : S) :
  brel_is_bottom S lteS b -> (∀ (a : S),  b <<= a -> a <<= b -> b [=] a) -> 
  ∀ (X W : finite_set S), snd(iterate_minset lteS W (b :: nil) X) [=MS] (b :: nil).
Proof. intros A A' X W. induction X. 
       + unfold iterate_minset. simpl. apply brel_minset_reflexive; auto. 
       + unfold iterate_minset.
         case_eq(find (below lteS a) X). 
         ++ intros s B.
            fold (iterate_minset lteS (a :: W) (b :: nil) X).
            rewrite (iterate_minset_invariant_0 _ lteS X (a :: W) W (b :: nil)).
            exact IHX.
         ++ intro B.
            case_eq(equiv lteS b a); intro R. 
            +++ destruct (equiv_elim _ _ _ _ R) as [R1 R2]. 
                assert (R' := A' a R2 R1). 
                assert (D : find (below lteS a) (b :: nil) = None).
                compute.
                assert (E: b <<= a). rewrite (lteCong _ _ _ _ R' (refS a)). apply lteRefl. 
                assert (F: a <<= b). rewrite (lteCong _ _ _ _ (refS a) R'). apply lteRefl. 
                rewrite E, F; auto. 
                rewrite D. 
                fold (iterate_minset lteS W (a :: b :: nil) X). 
                assert (E : (a :: b :: nil) [=S] (b::nil)).
                   compute. rewrite R'.  rewrite (symS _ _ R'). rewrite refS; auto.
                assert (F := iterate_minset_left_congruence_weak _ _ refS symS tranS _ lteCong X W _ _ E). 
                apply set_equal_implies_minset_equal in F. 
                exact (brel_minset_transitive _ _ _ F IHX). 

            +++ case_eq(find (below lteS a) (b :: nil)).
                ++++ intros s C. (* s must be bottom b *)
                     compute in C.
                     case_eq(lteS b a); intro D; case_eq(lteS a b); intro E. 
                     +++++ rewrite D in C. rewrite E in C. discriminate C. 
                     +++++ rewrite D in C. rewrite E in C. inversion C.
                           fold (iterate_minset lteS (a :: W) (s :: nil) X).
                           rewrite <- H0. 
                           assert (I := iterate_minset_invariant_0 _ lteS X (a :: W)  W (b :: nil)).
                           rewrite I.
                           exact IHX. 
                     +++++ rewrite D in C. discriminate C. 
                     +++++ rewrite D in C. discriminate C. 

                ++++ intro C.
                     assert (D := find_below_none _ _ refS symS lteS lteCong _ _ C).
                     assert (E := D _ (in_set_singleton_intro S rS symS _ _ (refS b))).
                     assert (F := A a).
                     apply below_false_elim in E.  
                     destruct E as [E | E]. 
                     +++++ rewrite F in E. discriminate E. 
                     +++++ assert (G : a [~] b). apply equiv_intro; auto. 
                           rewrite G in R. discriminate R.
Qed. 

Lemma minset_bottom_aux (X : finite_set S) (b : S) :
     brel_is_bottom S lteS b -> (∀ t : S, b <<= t → t <<= b → b [=] t) ->  
         ([ms] (b :: X)) [=MS] (b :: nil). 
Proof. intros A A'. unfold uop_minset. 
       unfold iterate_minset.        
       assert (B : find (below lteS b) X = None).
          case_eq(find (below lteS b) X); auto. 
             intros s C.  
             destruct (find_below_some _ _ refS symS _ _ _ _ C) as [D E]. 
             assert (F := A s). apply below_elim in E.
             rewrite F in E. destruct E as [_ E]. discriminate E. 
       rewrite B.
       assert (C : find (below lteS b) nil = None). compute; auto.
       rewrite C.       
       fold (iterate_minset lteS nil (b :: nil) X). 
       apply iterate_minset_bottom; auto. 
Qed.

                                    
Lemma minset_bottom_with_anti_symmetry2 (anti : brel_antisymmetric S rS lteS) (X : finite_set S) (b : S) :
    brel_is_bottom S lteS b -> ([ms] (b :: X)) [=MS] (b :: nil). 
Proof. intros A. assert (A' := anti b). apply minset_bottom_aux; auto. Qed. 

Lemma minset_bottom_without_anti_symmetry2 (X : finite_set S) (b : S) :
    brel_is_qo_bottom S rS lteS b -> ([ms] (b :: X)) [=MS] (b :: nil). 
Proof. intros [A A']. apply minset_bottom_aux; auto. Qed. 


Lemma bop_minset_union_exists_ann_is_bottom (b : S) :
     brel_is_bottom S lteS b -> (∀ t : S, b <<= t → t <<= b → b [=] t) ->  
     bop_is_ann (finite_set S) (brel_minset rS lteS) bop_minset_union (b :: nil). 
Proof. intros A A'. unfold brel_is_bottom in A.  unfold bop_is_ann. intro X.
          assert (B : ([ms] (b :: X)) [=MS] (b :: nil)).
             exact (minset_bottom_aux _ _ A A'). 
          assert (C : ([ms] ((b :: nil) [U] X)) [=MS] ([ms] (b :: X)) ). 
             assert (D :=  bop_union_cons_shift  X b). 
             apply set_equal_implies_minset_equal in D. 
             exact (uop_minset_congruence lteRefl lteTrans _ _ D). 
          assert (D : ([ms] (X [U] (b :: nil))) [=MS] ([ms] (b :: X)) ). 
             assert (D :=  bop_union_cons_shift_v2  X b). 
             apply set_equal_implies_minset_equal in D. 
             exact (uop_minset_congruence lteRefl lteTrans _ _ D). 
          split. 
          unfold bop_minset_union.
          assert (E := minset_union_uop_invariant (b :: nil) X).
          assert (F := minset_transitive _ _ _ E C). 
          exact (minset_transitive _ _ _ F B). 
          unfold bop_minset_union.
          unfold brel_minset. rewrite minset_singleton.
          assert (E := minset_union_uop_invariant X (b :: nil)).
          assert (F := minset_transitive _ _ _ E D). 
          exact (minset_transitive _ _ _ F B). 
Qed.

Lemma bop_minset_union_exists_ann_without_antisymmetry : brel_exists_qo_bottom S rS lteS ->
           bop_exists_ann (finite_set S) (brel_minset rS lteS) bop_minset_union. 
Proof. intros [b [A A']]. exists (b :: nil). apply (bop_minset_union_exists_ann_is_bottom b); auto. Defined. 


Lemma bop_minset_union_exists_ann_with_antisymmetry (anti : brel_antisymmetric S rS lteS) : 
      brel_exists_bottom S lteS ->
           bop_exists_ann (finite_set S) (brel_minset rS lteS) bop_minset_union. 
Proof. intros [b A].
       assert (B : brel_exists_qo_bottom S rS lteS). 
          exists b. split; auto. exact (anti b). 
       exact (bop_minset_union_exists_ann_without_antisymmetry B).
Defined.        


Lemma brel_not_antisymmetric_implies_bop_minset_union_not_selective :
         (brel_not_antisymmetric S rS lteS) → bop_not_selective (finite_set S) (brel_minset rS lteS) bop_minset_union. 
Proof. intros [ [s t] [[A B] C] ]. 
       exists (s :: nil, t :: nil). 
          unfold bop_minset_union.        
          unfold brel_minset.
          assert (D : (s :: nil) [U] (t :: nil) [=S] (s :: t :: nil)). (* extract as lemma *) 
             apply brel_set_intro; auto. split. 
                apply brel_subset_intro; auto. 
                intros u D. 
                apply in_set_bop_union_elim in D; auto. 
                apply in_set_cons_intro; auto.                 
                destruct D as [D | D]. 
                   left. apply in_set_cons_elim in D; auto.
                   destruct D as [D | D]; auto. 
                   compute in D. discriminate D.
                   right; auto.                    
                apply brel_subset_intro; auto. 
                intros u D. 
                apply in_set_cons_elim in D; auto. 
                apply in_set_bop_union_intro; auto.                 
                destruct D as [D | D]. 
                   left. apply in_set_cons_intro; auto.
                   right; auto. 
          assert (E : ([ms] ([ms] ((s :: nil) [U] (t :: nil)))) [=S] (s :: t :: nil)).
             assert (G : ([ms] ((s :: nil) [U] (t :: nil))) [=S] (s :: t :: nil)).
                assert (I : ([ms] (s :: t :: nil)) [=S] (s :: t :: nil)). 
                   unfold uop_minset. unfold iterate_minset. 
                   assert (J : List.find (below lteS s) (t :: nil) = None).
                      compute. rewrite A, B; auto. 
                    rewrite J. 
                    assert (K: List.find (below lteS s) nil = None). compute; auto. 
                    rewrite K. 
                    assert (L: List.find (below lteS t) nil = None). compute; auto. 
                    rewrite L. 
                    assert (M: List.find (below lteS t) (s :: nil) = None). 
                        compute. rewrite A, B; auto. 
                    rewrite M. 
                    compute. (* need a lemma here *)
                    rewrite refS. rewrite refS. rewrite refS. rewrite refS. rewrite C.
                    case_eq(rS t s); intro N; auto.
                    assert (J := uop_minset_congruence_weak _ _ D). 
                    exact (set_transitive _ _ _ J I).
             assert (H := uop_minset_idempotent ((s :: nil) [U] (t :: nil))).
                 exact (set_transitive _ _ _ H G).      
          split.
          rewrite minset_singleton. rewrite minset_singleton. 
          case_eq(brel_set rS ([ms] ([ms] ((s :: nil) [U] (t :: nil)))) (s :: nil)); intro F; auto. 
          apply set_symmetric in F. 
          assert (G := set_transitive _ _ _ F E). 
          compute in G.       
          rewrite C in G. rewrite refS in G. rewrite refS in G. 
          case_eq(rS t s); intro H.
             apply symS in H. rewrite H in C. discriminate C. 
             rewrite H in G. discriminate G. 

          rewrite minset_singleton. rewrite minset_singleton. 
          case_eq(brel_set rS ([ms] ([ms] ((s :: nil) [U] (t :: nil)))) (t :: nil)); intro F; auto. 
          apply set_symmetric in F. 
          assert (G := set_transitive _ _ _ F E). 
          compute in G.       
          rewrite C in G. rewrite refS in G. 
          case_eq(rS t s); intro H.
             apply symS in H. rewrite H in C. discriminate C. 
             rewrite H in G. discriminate G. 
Defined.              


Lemma bop_minset_union_incomp_pair (s t : S) (L : s !<<= t) (R : t !<<= s): ((s :: nil) <U> (t :: nil)) [<>MS] (s :: nil).
       unfold bop_minset_union.
       unfold brel_minset. 
       rewrite minset_singleton. rewrite minset_singleton. 
       case_eq(brel_set rS ([ms] ([ms] ((s :: nil) [U] (t :: nil)))) (s :: nil) ); intro A; auto.
       assert (B : ((s :: nil) [U] (t :: nil)) [=S] (s :: t :: nil)).
          apply brel_set_intro_prop; auto. split. 
             intros u B. apply in_set_bop_union_elim in B; auto. 
             destruct B as [B | B]. 
                apply in_set_singleton_elim in B; auto. 
                apply in_set_cons_intro; auto. 
                apply in_set_singleton_elim in B; auto. 
                apply in_set_cons_intro; auto. 
                right. apply in_set_cons_intro; auto. 
             intros u B. apply in_set_cons_elim in B; auto.
             destruct B as [B | B]. 
                apply in_set_bop_union_intro; auto. left. 
                apply in_set_cons_intro; auto. 
                apply in_set_bop_union_intro; auto. 
       assert (C : [ms] ((s :: nil) [U] (t :: nil)) [=S] [ms] (s :: t :: nil)).
          exact (uop_minset_congruence_weak _ _ B). 
       assert (D : [ms] ([ms] ((s :: nil) [U] (t :: nil))) [=S] [ms] ((s :: nil) [U] (t :: nil))).
          exact(uop_minset_idempotent ((s :: nil) [U] (t :: nil))).    
       assert (E : [ms] ([ms] ((s :: nil) [U] (t :: nil))) [=S] (s :: t :: nil)).
          assert (F := set_transitive _ _ _ D C). 
          assert (G : [ms] (s :: t :: nil) [=S] (s :: t :: nil)). 
             apply brel_set_intro_prop; auto. split. 
                intros u G. apply in_minset_elim in G; auto. destruct G as [G H]; auto. 
                intros u G. apply in_minset_intro; auto. split; auto. 
                   intros v H. apply in_set_cons_elim in G; apply in_set_cons_elim in H; auto. 
                   destruct G as [G | G]; destruct H as [H | H]. 
                      rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ G) (symS _ _ H)). 
                         apply below_not_reflexive; auto.  
                      apply in_set_singleton_elim in H; auto.
                      rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ G) (symS _ _ H)). 
                      apply below_false_intro; auto. 
                      apply in_set_singleton_elim in G; auto. 
                      rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ G) (symS _ _ H)). 
                      apply below_false_intro; auto. 
                      apply in_set_singleton_elim in H; apply in_set_singleton_elim in G; auto.
                      rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ G) (symS _ _ H)). 
                         apply below_not_reflexive; auto.  
          exact (set_transitive _ _ _ F G). 
       assert (F : (s:: t :: nil) [=S] (s :: nil)). apply set_symmetric in E. exact (set_transitive _ _ _ E A). 
       apply brel_set_elim in F. destruct F as [F _].
       assert (G : t [in] (s :: t :: nil)). compute. rewrite (refS t). case_eq(rS t s); intro; auto. 
       assert (H := brel_subset_elim _ _ symS tranS _ _ F t G). 
       compute in H.
       case_eq(rS t s); intro I. 
          rewrite (lteCong _ _ _ _ I (refS s)) in R.
          rewrite (lteRefl s) in R. discriminate R. 
          rewrite I in H. discriminate H.
Qed. 
  

Lemma bop_minset_union_not_selective : (brel_not_total S lteS) → bop_not_selective (finite_set S) (brel_minset rS lteS) bop_minset_union. 
Proof. intros [ [s t] [L R] ]. 
       exists (s :: nil, t :: nil). split.
       apply bop_minset_union_incomp_pair; auto. 
       assert (A := bop_minset_union_incomp_pair t s R L). 
       case_eq(brel_minset rS lteS ((s :: nil) <U> (t :: nil)) (t :: nil)); intro B; auto.
       assert (C := bop_minset_union_commutative (t :: nil) (s :: nil)). 
       assert (D := brel_minset_transitive _ _ _ C B). 
       rewrite D in A. discriminate A. 
Defined.


Lemma total_implies_singlton_minsets (tot : brel_total S lteS) (X : finite_set S) (anti : brel_antisymmetric S rS lteS):
            (nil [=S] X) + {s : S & (s :: nil) [=S] [ms] X}.
Proof. induction X.
       left. compute; auto. 
       right. destruct IHX as [IHX | [s A]]. 
          exists a.
          assert (A : [ms] (a :: X) [=S] (a :: nil)).
             assert (B : ([ms] (a :: X)) [=S] ([ms] (a :: nil))).
                assert (C : (a :: X) [=S] (a :: nil)).
                   apply brel_set_intro_prop; auto. split. 
                   intros s A. apply in_set_singleton_intro; auto. 
                   apply in_set_cons_elim in A; auto. destruct A as [A | A]; auto. 
                      rewrite <- (in_set_congruence _ _ symS tranS _ _ _ _ IHX (refS s)) in A. 
                      compute in A.  discriminate A. 
                   intros s A. apply in_set_singleton_elim in A; auto.                      
                   apply in_set_cons_intro; auto. 
               exact (uop_minset_congruence_weak _ _ C ). 
             rewrite minset_singleton in B. auto. 
          apply set_symmetric; auto.

          apply brel_set_elim_prop in A; auto. destruct A as [A B].
          assert (C : s [in] (s :: nil)). apply in_set_cons_intro; auto. 
          assert (D := A s C). 
          apply in_minset_elim in D; auto. destruct D as [D E]. 
          destruct (tot a s) as [F | F]. 
             exists a. 
             apply brel_set_intro_prop; auto. split. 
                intros t G. apply in_set_singleton_elim in G; auto. 
                rewrite (lteCong _ _ _ _ G (refS s)) in F.  
                apply in_minset_intro; auto. split. 
                   apply in_set_cons_intro; auto. 
                   intros u H. apply below_false_intro; auto. 
                   apply in_set_cons_elim in H; auto. 
                   destruct H as [H | H]. 
                      right. apply symS in G. apply symS in H. 
                      rewrite (lteCong _ _ _ _ G H). exact (lteRefl a). 
                      assert (I := E u H). apply below_false_elim in I. 
                      destruct I as [I | I]. 
                         left. case_eq(lteS u t); intro J; auto. 
                            rewrite (lteTrans _ _ _ J F) in I. discriminate I. 
                         right. exact (lteTrans _ _ _ F I). 
                intros t G. apply in_minset_elim in G; auto. destruct G as [G H]. 
                assert (I : s [in] (a :: X)). apply in_set_cons_intro; auto.              
                assert (J := H s I). apply below_false_elim in J; auto. 
                apply in_set_cons_elim in G; auto.
                (* this is a mess *) 
                destruct G as [G | G]; destruct J as [J | J]. 
                   apply in_set_singleton_intro; auto. 
                   apply in_set_singleton_intro; auto. 
                   assert (Z : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                   assert (W := H a Z). apply below_false_elim in W; auto. 
                      destruct W as [W | W]. 
                         destruct (tot a t) as [Y | Y]; destruct (tot s t) as [U | U]. 
                           rewrite Y in W. discriminate W. 
                           rewrite Y in W. discriminate W. 
                           rewrite U in J. discriminate J. 
                           assert (V := E t G). apply below_false_elim in V; auto.
                               destruct V as [V | V]. 
                                  rewrite U in V. discriminate V. 
                                  rewrite V in J. discriminate J. 
                         assert (Y : t [in] [ms] X). 
                            apply in_minset_intro; auto. split; auto. 
                            intros u Y. apply H. apply in_set_cons_intro; auto. 
                         assert (U := B t Y). apply in_set_singleton_elim in U; auto. 
                         rewrite (lteCong _ _ _ _ U (refS t)) in J. rewrite (lteRefl t) in J. discriminate J. 
                   assert (K := E t G). apply below_false_elim in K; auto.
                   destruct K as [K | K]. 
                      rewrite J in K. discriminate K. 
                      assert (L := anti _ _ K J). 
                      rewrite (lteCong _ _ _ _ (refS a) L) in F. 
                      apply in_set_singleton_intro; auto. 
                      case_eq(rS a t); intro M; auto.                       
                         case_eq(lteS t a); intro N. 
                            rewrite (anti _ _ F N) in M. discriminate M. 
                            assert (O : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                            assert (P := H a O). apply below_false_elim in P; auto. 
                               destruct P as [P | P]. 
                                  rewrite F in P. discriminate P. 
                                  rewrite P in N. discriminate N. 
                              
             exists s.
             apply brel_set_intro_prop; auto; split. 
                intros t G. apply in_set_singleton_elim in G; auto. 
                rewrite (lteCong _ _ _ _ G (refS a)) in F. 
                apply in_minset_intro; auto. split.                 
                   apply in_set_cons_intro; auto. right.
                   apply (in_set_right_congruence _ _ symS tranS _ _ X G); auto. 
                   intros u H. apply in_set_cons_elim in H; auto. 
                   destruct H as [H | H]. 
                      apply below_false_intro; auto. 
                      right. rewrite (lteCong _ _ _ _ (refS t) (symS _ _ H)). exact F. 
                      assert (I := E u H). rewrite (below_congruence _ _ _ lteCong _ _ _ _ G (refS u)) in I. 
                      exact I. 
                intros t G. apply in_minset_elim in G; auto.
                destruct G as [G H].  apply in_set_cons_elim in G; auto. 
                destruct G as [G | G]. 
                   rewrite (lteCong _ _ _ _ (refS s) G) in F. 
                   assert (I : s [in] (a :: X)). apply in_set_cons_intro; auto. 
                   assert (J := H s I). apply below_false_elim in J; auto.
                   destruct J as [J | J]. 
                      rewrite F in J. discriminate J. 
                      apply in_set_singleton_intro; auto.                    
                   assert (I : t [in] ([ms] X)).
                      apply in_minset_intro; auto. split; auto. 
                         intros u I. apply H. apply in_set_cons_intro; auto. 
                   exact (B t I).                 
Qed.


Lemma bop_minset_union_nil_left_v2 (X Y : finite_set S) : nil [=S] X -> (X <U> Y) [=S] ([ms] Y).
Proof. intro A. 
       assert (B := bop_minset_union_congruence_weak _ _ _ _ A (set_reflexive Y)). 
       apply set_symmetric in B. 
       assert (C : (nil <U> Y) [=S] ([ms] Y)). 
          unfold bop_minset_union. 
          rewrite minset_empty. 
          assert (C := bop_union_with_nil_left _ rS refS symS tranS ([ms] Y)). 
          assert (D := uop_minset_congruence_weak _ _ C). 
          assert (E := uop_minset_idempotent Y). 
          exact (set_transitive _ _ _ D E). 
       exact (set_transitive _ _ _ B C). 
Qed. 

Lemma bop_minset_union_nil_right_v2 (X Y : finite_set S) : nil [=S] Y -> (X <U> Y) [=S] ([ms] X). 
Proof. intro A.
       assert (B := bop_minset_union_nil_left_v2 Y X A). 
       assert (C : (X <U> Y) [=S] (Y <U> X)).
          unfold bop_minset_union.
          apply minset_union_commutative_weak. 
       exact (brel_set_transitive _ _ refS symS tranS _ _ _ C B).        
Qed. 
       
Lemma bop_minset_union_selective_weak (tot : brel_total S lteS) (anti : brel_antisymmetric S rS lteS) (X Y : finite_set S):
  (X <U> Y) [=S] ([ms] X) + (X <U> Y) [=S] ([ms] Y). 
Proof. destruct(total_implies_singlton_minsets tot X) as [A | A];
       destruct(total_implies_singlton_minsets tot Y) as [B | B]; auto. 
          left. apply bop_minset_union_nil_right_v2; auto. 
          right. apply bop_minset_union_nil_left_v2; auto. 
          left.  apply bop_minset_union_nil_right_v2; auto. 
          destruct A as [x A]. destruct B as [y B].
          unfold bop_minset_union.
          assert (F := bop_union_congruence _ _ _ _ A B).
          assert (G := uop_minset_congruence_weak _ _ F). 
          assert (H : (x :: nil) [U] (y :: nil) [=S] (x :: y :: nil)).
             apply brel_set_intro_prop; auto. split. 
                intros t C. apply in_set_bop_union_elim in C; auto.
                destruct C as [C | C]. 
                   apply in_set_singleton_elim in C; auto.
                   apply in_set_cons_intro; auto. 
                   apply in_set_cons_intro; auto. 
                intros t C. apply in_set_bop_union_intro; auto. 
                apply in_set_cons_elim in C; auto. 
                destruct C as [C | C]. 
                   left. apply in_set_singleton_intro; auto. 
                   right. auto.                    
          assert (I := uop_minset_congruence_weak _ _ H).           
          apply brel_set_symmetric in G. 
          assert (J := brel_set_transitive _ _ refS symS tranS _ _ _ G I).

          assert (A' := A). assert(B' := B). 
          apply brel_set_elim_prop in A; auto. destruct A as [A1 A2].
          apply brel_set_elim_prop in B; auto. destruct B as [B1 B2].
          
          case_eq(lteS x y); intro C;  case_eq(lteS y x); intro D.  
            (* x ~ y *)
            assert (E := anti _ _ C D). left.
            assert (K : [ms] (x :: y :: nil) [=S] ([ms] X)).
               apply brel_set_intro_prop; auto. split. 
                  intros t K. apply A1. apply in_set_singleton_intro; auto. 
                  apply in_minset_elim in K; auto. destruct K as [K1 K2]. 
                  apply in_set_cons_elim in K1; auto.
                  destruct K1 as [K1 | K1]. 
                     exact K1. 
                     apply in_set_cons_elim in K1; auto.
                     destruct K1 as [K1 | K1]. 
                        exact (tranS _ _ _ E K1). 
                        compute in K1. discriminate K1. 
                     
                  intros t K. assert (L := A2 t K). 
                  apply in_set_singleton_elim in L; auto. 
                  apply in_minset_intro; auto. split. 
                     apply in_set_cons_intro; auto. 
                     intros u M. apply in_set_cons_elim in M; auto. 
                     destruct M as [M | M]. 
                        rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ L) (symS _ _ M)). 
                        apply below_not_reflexive; auto. 
                        apply in_set_singleton_elim in M; auto. 
                        assert (N := tranS _ _ _ E M). 
                        rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ L) (symS _ _ N)). 
                        apply below_not_reflexive; auto.                         
            exact (brel_set_transitive _ _ refS symS tranS _ _ _ J K). 

            (* x < y *)  
            left.
            assert (K : [ms] (x :: y :: nil) [=S] ([ms] X)).
               assert (K : [ms] (x :: y :: nil) [=S] (x :: nil)). 
                  apply brel_set_intro_prop; auto. split. 
                     intros t K. apply in_set_singleton_intro; auto. 
                     apply in_minset_elim in K; auto. destruct K as [K1 K2]. 
                     apply in_set_cons_elim in K1; auto.
                     destruct K1 as [K1 | K1]; auto. 
                        apply in_set_singleton_elim in K1; auto. 
                        assert (M : x [in] (x :: y :: nil)). apply in_set_cons_intro; auto. 
                        assert (N := K2 x M). 
                        rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ K1) (refS x)) in N. 
                        apply below_false_elim in N; auto. 
                        destruct N as [N | N]. 
                           rewrite C in N. discriminate N. 
                           rewrite N in D. discriminate D.
                     intros t K. apply in_set_singleton_elim in K; auto. 
                     apply in_minset_intro; auto. split. 
                        apply in_set_cons_intro; auto. 
                        intros u L. apply in_set_cons_elim in L; auto.                       
                        destruct L as [L | L]. 
                           rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ K) (symS _ _ L)). 
                           apply below_not_reflexive; auto. 
                           apply in_set_singleton_elim in L; auto.                   
                           rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ K) (symS _ _ L)). 
                           apply below_false_intro; auto. 
               exact (brel_set_transitive _ _ refS symS tranS _ _ _ K A'). 
            exact (brel_set_transitive _ _ refS symS tranS _ _ _ J K). 


            (* y < x *)
            right. assert (K : [ms] (x :: y :: nil) [=S] ([ms] Y)).
               assert (K : [ms] (x :: y :: nil) [=S] (y :: nil)). 
                  apply brel_set_intro_prop; auto. split. 
                     intros t K. apply in_set_singleton_intro; auto. 
                     apply in_minset_elim in K; auto. destruct K as [K1 K2]. 
                     apply in_set_cons_elim in K1; auto.
                     destruct K1 as [K1 | K1]; auto. 
                        assert (M : y [in] (x :: y :: nil)).
                           apply in_set_cons_intro; auto. right.
                           apply in_set_cons_intro; auto.                            
                        assert (N := K2 y M). 
                        rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ K1) (refS y)) in N. 
                        apply below_false_elim in N; auto. 
                        destruct N as [N | N]. 
                           rewrite D in N. discriminate N. 
                           rewrite N in C. discriminate C.
                        apply in_set_singleton_elim in K1; auto. 

                     intros t K. apply in_set_singleton_elim in K; auto. 
                     apply in_minset_intro; auto. split. 
                        apply in_set_cons_intro; auto. right. apply in_set_cons_intro; auto. 
                        intros u L. apply in_set_cons_elim in L; auto.                       
                        destruct L as [L | L]. 
                           rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ K) (symS _ _ L)).
                           apply below_false_intro; auto. 
                           apply in_set_singleton_elim in L; auto.                   
                           rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ K) (symS _ _ L)). 
                           apply below_not_reflexive; auto. 

               exact (brel_set_transitive _ _ refS symS tranS _ _ _ K B'). 
            exact (brel_set_transitive _ _ refS symS tranS _ _ _ J K). 

            (* x # y *)
            destruct (tot x y) as [E | E].
               rewrite E in C. discriminate C.
               rewrite E in D. discriminate D. 
Qed. 
          
Lemma bop_minset_union_selective (tot : brel_total S lteS) (anti : brel_antisymmetric S rS lteS) :
  bop_selective (finite_set S) (brel_minset rS lteS) bop_minset_union. 
Proof. intros X Y.
       destruct (bop_minset_union_selective_weak tot anti X Y) as [B | B]. 
       left. unfold brel_minset. unfold bop_minset_union.
       unfold bop_minset_union in B. 
       assert (C := uop_minset_idempotent (([ms] X) [U] ([ms] Y))). 
       exact (brel_set_transitive _ _ refS symS tranS _ _ _ C B). 
       right. unfold brel_minset. unfold bop_minset_union.
       unfold bop_minset_union in B. 
       assert (C := uop_minset_idempotent (([ms] X) [U] ([ms] Y))). 
       exact (brel_set_transitive _ _ refS symS tranS _ _ _ C B). 
Qed.


Definition bop_minset_union_selective_decide_v1 (tot_d : brel_total_decidable S lteS) (anti : brel_antisymmetric S rS lteS): 
      bop_selective_decidable (finite_set S) (brel_minset rS lteS) bop_minset_union
 := match tot_d with
     | inl tot  => inl (bop_minset_union_selective tot anti) 
     | inr ntot => inr (bop_minset_union_not_selective ntot)
    end.


Definition bop_minset_union_selective_decide_v2 
           (tot_d : brel_total_decidable S lteS)
           (anti_d : brel_antisymmetric_decidable S rS lteS): 
  bop_selective_decidable (finite_set S) (brel_minset rS lteS) bop_minset_union
:= match anti_d with
   | inl anti => match tot_d with
                 | inl tot  => inl (bop_minset_union_selective tot anti) 
                 | inr ntot => inr (bop_minset_union_not_selective ntot)
                 end
   | inr nanti => inr (brel_not_antisymmetric_implies_bop_minset_union_not_selective nanti)
   end. 


(* ann *)

(*
move this ... 
*)
Lemma lte_trichotomy (s t : S ) : s << t + t << s + s [~|#] t.
Proof. case_eq(below lteS s t); intro A;  case_eq(below lteS t s); intro B; auto. 
       apply below_false_elim in A. apply below_false_elim in B.
       destruct A as [A | A]; destruct B as [B | B]. 
          right. apply equiv_or_incomp_intro. right. apply incomp_intro; auto.
          rewrite B in A. discriminate A. 
          rewrite B in A. discriminate A.
          right. apply equiv_or_incomp_intro. left. apply equiv_intro; auto.
Qed. 


(* this is really a general lemma about antichains *) 
Lemma bottoms_is_minimal (BOTTOMS : finite_set S) (AC : is_antichain S rS lteS BOTTOMS) : 
  [ms] BOTTOMS [=S] BOTTOMS.
Proof. apply brel_set_intro_prop; auto. split. 

          intros a A. apply in_minset_elim in A; auto. 
          destruct A as [A _]. exact A. 

          intros a A. apply in_minset_intro; auto. split. 
             exact A. 
             intros t B.  assert (C := AC a A t B). apply equiv_or_incomp_elim in C.
             apply below_false_intro. 
             destruct C as [C | C]. 
                apply equiv_elim in C. destruct C as [C _]. right; exact C. 
                apply incomp_elim in C. destruct C as [_ C]. left; exact C. 
Qed.


Lemma bop_minset_union_enum_is_ann_left
      (BOTTOMS : finite_set S)
      (AC : is_antichain S rS lteS BOTTOMS)
      (*EC : ∀ s x : S, x [in] BOTTOMS -> s [~] x -> s [in] BOTTOMS*) 
      (w : S → S)
      (H :  ∀ s : S, (s [in] BOTTOMS) + ((w s) [in] BOTTOMS * (w s) << s)) 
      (* H :  ∀ s : S, (w s) [in] BOTTOMS * (w s) <<= s *)
      :
  ∀ X : finite_set S, (BOTTOMS <U> X) [=MS] BOTTOMS. 
Proof. intro X.
       assert (A : (BOTTOMS <U> X) [=S] BOTTOMS).
          apply brel_set_intro_prop; auto. split. 
             intros s B. unfold bop_minset_union in B. 
             apply in_minset_elim in B; auto. destruct B as [B C].
             apply in_set_bop_union_elim in B; auto. 
             destruct B as [B | B].
                (* B : s [in] ([ms] BOTTOMS) *) 
                apply in_minset_elim in B; auto. destruct B as [B _]. exact B.

                (* B : s [in] ([ms] X) *)                    
(* H             
                destruct (H s) as [E F].
                assert (G : (w s) [in] (([ms] BOTTOMS) [U] ([ms] X))).
                   apply in_set_bop_union_intro; auto. 
                   left. rewrite (in_set_congruence _ rS symS tranS _ _ _ _ (bottoms_is_minimal BOTTOMS AC) (refS (w s))).
                   exact E. 
 *)
                destruct (H s) as [Q | [E F]].
                   exact Q. 

                   assert (G : (w s) [in] (([ms] BOTTOMS) [U] ([ms] X))).
                      apply in_set_bop_union_intro; auto. 
                      left. rewrite (in_set_congruence _ rS symS tranS _ _ _ _ (bottoms_is_minimal BOTTOMS AC) (refS (w s))).
                      exact E. 
                

                   assert (I := C (w s) G). apply below_false_elim in I.
                   destruct I as [I | I].
                      (* new *) apply below_elim in F. destruct F as [F _]. 
                      rewrite I in F. discriminate F.

(* H                       
                   assert (J : s [~] (w s)). apply equiv_intro; auto. 
                   exact (EC s (w s) E J). 
 *)
                      assert (J : w s << w s). exact (below_pseudo_transitive_right _ lteS lteTrans _ _ _ F I).
                      rewrite (below_not_reflexive S lteS  (w s)) in J. discriminate J. 
                   
             intros s B. unfold bop_minset_union. apply in_minset_intro; auto. split. 
                apply in_set_bop_union_intro; auto. left. 
                rewrite (in_set_congruence _ rS symS tranS _ _ _ _ (bottoms_is_minimal BOTTOMS AC) (refS s)).
                exact B. 

                intros t C. case_eq(below lteS s t); intro D; auto. 
                   apply in_set_bop_union_elim in C; auto. 
                   destruct C as [C | C].
                      rewrite (in_set_congruence _ rS symS tranS _ _ _ _ (bottoms_is_minimal BOTTOMS AC) (refS t)) in C.
                      assert (E := AC s B t C). apply equiv_or_incomp_elim in E.
                      apply below_elim in D. destruct D as [D1 D2].                       
                      destruct E as [E | E].
                         apply equiv_elim in E. destruct E as [E1 E2]. 
                         rewrite E1 in D2. discriminate D2.

                         apply incomp_elim in E. destruct E as [E1 E2]. 
                         rewrite E2 in D1. discriminate D1. 
                         
                      apply in_minset_elim in C; auto. destruct C as [C E].
(* H                         
                      destruct (H t) as [F G].
                      assert (I : w t << s).  exact (below_pseudo_transitive_left _ lteS lteTrans _ _ _ G D).
                      apply below_elim in I. destruct I as [I K]. 
                      assert (J := AC s B (w t) F). apply equiv_or_incomp_elim in J.
                      destruct J as [J | J]. 
                         apply equiv_elim in J. destruct J as [J1 J2]. 
                         rewrite J1 in K. discriminate K.
                         apply incomp_elim in J. destruct J as [J1 J2]. 
                         rewrite J2 in I. discriminate I.
 *)
                      destruct (H t) as [Q | [F G]].
                         assert (F := AC s B t Q). apply equiv_or_incomp_elim in F.
                         apply below_elim in D. destruct D as [D1 D2].
                         destruct F as [F | F]. 
                            apply equiv_elim in F. destruct F as [F1 F2]. 
                            rewrite F1 in D2. discriminate D2. 

                            apply incomp_elim in F. destruct F as [F1 F2]. 
                            rewrite F2 in D1. discriminate D1. 
                         
                         assert (I : w t << s).  exact (below_transitive _ lteS lteTrans _ _ _ G D).
                         apply below_elim in I. destruct I as [I K]. 
                         assert (J := AC s B (w t) F). apply equiv_or_incomp_elim in J.
                         destruct J as [J | J]. 
                            apply equiv_elim in J. destruct J as [J1 J2]. 
                            rewrite J1 in K. discriminate K.
                            apply incomp_elim in J. destruct J as [J1 J2]. 
                            rewrite J2 in I. discriminate I.
                      
                         
       apply set_equal_implies_minset_equal; auto. 
Qed.

Lemma bop_minset_union_enum_is_ann_right
      (BOTTOMS : finite_set S)
      (AC : is_antichain S rS lteS BOTTOMS)
      (w : S → S)
      (H :  ∀ s : S, (s [in] BOTTOMS) + ((w s) [in] BOTTOMS * (w s) << s)) :
  ∀ X : finite_set S, (X <U> BOTTOMS) [=MS] BOTTOMS. 
Proof. intro X.
       assert (A := bop_minset_union_commutative X BOTTOMS).
       assert (B := bop_minset_union_enum_is_ann_left BOTTOMS AC w H X). 
       assert (C := brel_minset_transitive _ _ _ A B). 
       exact C.
Qed.        
                 
Lemma bop_minset_union_enum_is_ann_aux
      (BOTTOMS : finite_set S)
      (AC : is_antichain S rS lteS BOTTOMS)
      (w : S → S)
      (H :  ∀ s : S, (s [in] BOTTOMS) + ((w s) [in] BOTTOMS * (w s) << s)) :
        bop_is_ann (finite_set S) (brel_minset rS lteS) bop_minset_union BOTTOMS. 
Proof. intro X. split. 
          (* (BOTTOMS <U> X) [=MS] BOTTOMS *) 
          apply (bop_minset_union_enum_is_ann_left BOTTOMS AC w H X). 
          (* (X <U> BOTTOMS) [=MS] BOTTOMS *)
          apply (bop_minset_union_enum_is_ann_right BOTTOMS AC w H X). 
Qed.


Lemma bop_minset_union_enum_is_ann (bf : bottoms_set_is_finite S rS lteS) : 
  bop_is_ann (finite_set S) (brel_minset rS lteS) bop_minset_union (fst (projT1 bf)).
Proof. destruct bf as [[BOTTOMS w] [AC H]]. apply (bop_minset_union_enum_is_ann_aux BOTTOMS AC w H). Defined. 

Lemma bop_minset_union_exists_ann (bf : bottoms_set_is_finite S rS lteS) : 
   bop_exists_ann (finite_set S) (brel_minset rS lteS) bop_minset_union.
Proof. exists (fst (projT1 bf)).
       apply (bop_minset_union_enum_is_ann bf). 
Defined. 

(* number 2 *) 


Lemma bop_minset_union_enum_is_ann_left2
      (BOTTOMS : finite_set S)
      (AC : is_antichain S rS lteS BOTTOMS)
      (w : S → S)
      (H :  ∀ s : S, (w s) [in] BOTTOMS * (w s) << s)
      :
  ∀ X : finite_set S, (BOTTOMS <U> X) [=MS] BOTTOMS. 
Proof. intro X.
       assert (A : (BOTTOMS <U> X) [=S] BOTTOMS).
          apply brel_set_intro_prop; auto. split. 
             intros s B. unfold bop_minset_union in B. 
             apply in_minset_elim in B; auto. destruct B as [B C].
             apply in_set_bop_union_elim in B; auto. 
             destruct B as [B | B].
                (* B : s [in] ([ms] BOTTOMS) *) 
                apply in_minset_elim in B; auto. destruct B as [B _]. exact B.

                (* B : s [in] ([ms] X) *)                    
                destruct (H s) as [E F].

                   assert (G : (w s) [in] (([ms] BOTTOMS) [U] ([ms] X))).
                      apply in_set_bop_union_intro; auto. 
                      left. rewrite (in_set_congruence _ rS symS tranS _ _ _ _ (bottoms_is_minimal BOTTOMS AC) (refS (w s))).
                      exact E. 
                

                   assert (I := C (w s) G). apply below_false_elim in I.
                   destruct I as [I | I].
                      (* new *) apply below_elim in F. destruct F as [F _]. 
                      rewrite I in F. discriminate F.

                      assert (J : w s << w s). exact (below_pseudo_transitive_right _ lteS lteTrans _ _ _ F I).
                      rewrite (below_not_reflexive S lteS (w s)) in J. discriminate J. 
                   
             intros s B. unfold bop_minset_union. apply in_minset_intro; auto. split. 
                apply in_set_bop_union_intro; auto. left. 
                rewrite (in_set_congruence _ rS symS tranS _ _ _ _ (bottoms_is_minimal BOTTOMS AC) (refS s)).
                exact B. 

                intros t C. case_eq(below lteS s t); intro D; auto. 
                   apply in_set_bop_union_elim in C; auto. 
                   destruct C as [C | C].
                      rewrite (in_set_congruence _ rS symS tranS _ _ _ _ (bottoms_is_minimal BOTTOMS AC) (refS t)) in C.
                      assert (E := AC s B t C). apply equiv_or_incomp_elim in E.
                      apply below_elim in D. destruct D as [D1 D2].                       
                      destruct E as [E | E].
                         apply equiv_elim in E. destruct E as [E1 E2]. 
                         rewrite E1 in D2. discriminate D2.

                         apply incomp_elim in E. destruct E as [E1 E2]. 
                         rewrite E2 in D1. discriminate D1. 
                         
                      apply in_minset_elim in C; auto. destruct C as [C E].
                      destruct (H t) as [F G].
                         
                         assert (I : w t << s).  exact (below_transitive _ lteS lteTrans _ _ _ G D).
                         apply below_elim in I. destruct I as [I K]. 
                         assert (J := AC s B (w t) F). apply equiv_or_incomp_elim in J.
                         destruct J as [J | J]. 
                            apply equiv_elim in J. destruct J as [J1 J2]. 
                            rewrite J1 in K. discriminate K.
                            apply incomp_elim in J. destruct J as [J1 J2]. 
                            rewrite J2 in I. discriminate I.
                      
                         
       apply set_equal_implies_minset_equal; auto. 
Qed.


Lemma bop_minset_union_enum_is_ann_right2
      (BOTTOMS : finite_set S)
      (AC : is_antichain S rS lteS BOTTOMS)
      (w : S → S)
      (H :  ∀ s : S, ((w s) [in] BOTTOMS * (w s) << s)) :
  ∀ X : finite_set S, (X <U> BOTTOMS) [=MS] BOTTOMS. 
Proof. intro X.
       assert (A := bop_minset_union_commutative X BOTTOMS).
       assert (B := bop_minset_union_enum_is_ann_left2 BOTTOMS AC w H X). 
       assert (C := brel_minset_transitive _ _ _ A B). 
       exact C.
Qed.        

Lemma bop_minset_union_enum_is_ann_aux2
      (BOTTOMS : finite_set S)
      (AC : is_antichain S rS lteS BOTTOMS)
      (w : S → S)
      (H :  ∀ s : S, ((w s) [in] BOTTOMS * (w s) << s)) :
        bop_is_ann (finite_set S) (brel_minset rS lteS) bop_minset_union BOTTOMS. 
Proof. intro X. split. 
          (* (BOTTOMS <U> X) [=MS] BOTTOMS *) 
          apply (bop_minset_union_enum_is_ann_left2 BOTTOMS AC w H X). 
          (* (X <U> BOTTOMS) [=MS] BOTTOMS *)
          apply (bop_minset_union_enum_is_ann_right2 BOTTOMS AC w H X). 
Qed.


Lemma bop_minset_union_enum_is_ann2 (bf : bottoms_set_is_finite2 S rS lteS) : 
  bop_is_ann (finite_set S) (brel_minset rS lteS) bop_minset_union (fst (projT1 bf)).
Proof. destruct bf as [[BOTTOMS w] [AC H]]. apply (bop_minset_union_enum_is_ann_aux2 BOTTOMS AC w H). Defined. 



Lemma bop_minset_union_not_exists_ann_aux (bnf : bottoms_set_not_is_finite S rS lteS) : 
  ∀ X : finite_set S, {Z : finite_set S & (Z <U> X) [<>MS] X}.
Proof. intro X. destruct bnf as [F P].
       exists ((F ([ms] X)) :: nil).
       assert (Q := P ([ms] X) (uop_minset_is_antichain X)). destruct Q as [Q1 Q2].

       unfold brel_minset.
       case_eq(brel_set rS ([ms] ((F ([ms] X) :: nil) <U> X)) ([ms] X)); intro A; auto.
          apply brel_set_elim_prop in A; auto. destruct A as [A _].
          assert (B : F ([ms] X) [in] ([ms] ((F ([ms] X) :: nil) <U> X))).           
             apply in_minset_intro; auto. split. 
                unfold bop_minset_union.
                apply in_minset_intro; auto. split. 
                   apply in_set_bop_union_intro; auto. 
                   left. rewrite minset_singleton. apply in_set_singleton_intro; auto. 
                   
                   intros t B. apply in_set_bop_union_elim in B; auto. 
                   destruct B as [B | B].
                      rewrite minset_singleton in B. apply in_set_singleton_elim in B; auto. 
                      apply symS in B. rewrite (below_congruence S rS lteS lteCong _ _ _ _ (refS (F ([ms] X))) B). 
                      apply (below_not_reflexive S lteS).

                      exact (Q2 t B). 
                
                unfold bop_minset_union.
                intros t D. 
                apply in_minset_elim in D; auto. destruct D as [D1 D2].
                apply in_set_bop_union_elim in D1; auto.
                destruct D1 as [D1 | D1]. 
                   rewrite minset_singleton in D1. apply in_set_singleton_elim in D1; auto. 
                   apply symS in D1. rewrite (below_congruence S rS lteS lteCong _ _ _ _ (refS (F ([ms] X))) D1). 
                   apply (below_not_reflexive S lteS).
                   
                   exact (Q2 _ D1).
             
          assert (D := A _ B). rewrite D in Q1. discriminate Q1. 
Qed.



(*
Lemma bop_minset_union_not_exists_ann_aux2 (bnf : bottoms_set_not_is_finite2 S rS lteS) : 
  ∀ X : finite_set S, {Z : finite_set S & (Z <U> X) [<>MS] X}.
Proof. intro X. destruct bnf as [F P].
       exists ((F ([ms] X)) :: nil).
       assert (Q := P ([ms] X) (uop_minset_is_antichain X)). 

       unfold brel_minset.
       case_eq(brel_set rS ([ms] ((F ([ms] X) :: nil) <U> X)) ([ms] X)); intro A; auto.
          apply brel_set_elim_prop in A; auto. destruct A as [A _].
          assert (B : F ([ms] X) [in] ([ms] ((F ([ms] X) :: nil) <U> X))).           
             apply in_minset_intro; auto. split. 
                unfold bop_minset_union.
                apply in_minset_intro; auto. split. 
                   apply in_set_bop_union_intro; auto. 
                   left. rewrite minset_singleton. apply in_set_singleton_intro; auto. 
                   
                   intros t B. apply in_set_bop_union_elim in B; auto. 
                   destruct B as [B | B].
                      rewrite minset_singleton in B. apply in_set_singleton_elim in B; auto. 
                      apply symS in B. rewrite (below_congruence S rS lteS lteCong _ _ _ _ (refS (F ([ms] X))) B). 
                      apply (below_not_reflexive S lteS).

                      exact (Q t B). 
                
                unfold bop_minset_union.
                intros t D. 
                apply in_minset_elim in D; auto. destruct D as [D1 D2].
                apply in_set_bop_union_elim in D1; auto.
                destruct D1 as [D1 | D1]. 
                   rewrite minset_singleton in D1. apply in_set_singleton_elim in D1; auto. 
                   apply symS in D1. rewrite (below_congruence S rS lteS lteCong _ _ _ _ (refS (F ([ms] X))) D1). 
                   apply (below_not_reflexive S lteS).
                   
                   exact (Q _ D1).
             
         assert (D := A _ B).
         assert (E := Q _ D).
         admit.    (* this does not seem to work!  *)
Admitted. 
*) 

       
Lemma bop_minset_union_not_exists_ann (bnf : bottoms_set_not_is_finite S rS lteS) : 
  bop_not_exists_ann (finite_set S) (brel_minset rS lteS) bop_minset_union.
Proof. unfold bop_not_exists_ann. intros X. 
       destruct (bop_minset_union_not_exists_ann_aux bnf X) as [Z A]. 
       exists Z. right. exact A. 
Defined. 


Definition bottoms_set_is_finite_decidable  (T : Type) (eq lte : brel T) :=
  (bottoms_set_is_finite T eq lte) + (bottoms_set_not_is_finite T eq lte).


Definition bop_minset_union_exists_ann_decide (bf_d : bottoms_set_is_finite_decidable S rS lteS) :
      bop_exists_ann_decidable (finite_set S) (brel_minset rS lteS) bop_minset_union
 := match bf_d with
     | inl p  => inl (bop_minset_union_exists_ann p) 
     | inr p => inr (bop_minset_union_not_exists_ann p)
    end.


Lemma bop_minset_union_is_glb_wrt_lte_left : bop_is_glb (brel_lte_left (brel_minset rS lteS) bop_minset_union) bop_minset_union.
Proof. apply bop_is_glb_wrt_lte_left.
       apply brel_minset_reflexive; auto. 
       apply brel_minset_symmetric; auto. 
       apply brel_minset_transitive; auto. 
       apply bop_minset_union_associative; auto.
       apply bop_minset_union_congruence; auto.        
       apply bop_minset_union_idempotent; auto.        
       apply bop_minset_union_commutative; auto.        
Qed. 


Lemma bop_union_is_lub_wrt_lte_right : bop_is_lub (brel_lte_right (brel_minset rS lteS) bop_minset_union) bop_minset_union.
Proof. apply bop_is_lub_wrt_lte_right. 
       apply brel_minset_reflexive; auto. 
       apply brel_minset_symmetric; auto. 
       apply brel_minset_transitive; auto. 
       apply bop_minset_union_associative; auto.
       apply bop_minset_union_congruence; auto. 
       apply bop_minset_union_idempotent; auto.        
       apply bop_minset_union_commutative; auto.        
Qed. 

(*
Lemma minset_subset_implies_lte_right (X Y : finite_set S) (A : brel_minset_subset rS lteS X Y = true) :
       brel_lte_right (brel_minset rS lteS) bop_minset_union X Y = true. 
Proof. unfold brel_lte_right. unfold brel_minset. 
       apply brel_set_intro. split. 
       - apply brel_subset_minset_union_right. 
       - unfold brel_minset_subset in A.
         assert (B := brel_subset_elim _ _ symS tranS _ _ A). 
         apply brel_subset_intro; auto. 
         intros a C.
         apply in_minset_intro; auto. 
         apply in_minset_elim in C; auto. destruct C as [C D].
         apply in_minset_elim in C; auto. destruct C as [C E].
         apply in_set_bop_union_elim in C; auto. 
         destruct C as [C | C]; split.
         + assert (F := B _ C).
           apply in_minset_elim in F; auto. destruct F as [F _].
           exact F. 
         + intros t F.
           assert (G := B _ C).
           apply in_minset_elim in G; auto. destruct G as [G H].
           apply H; auto. 
         + apply in_minset_elim in C; auto. destruct C as [C F].
           exact C.
         + intros t F. 
           apply in_minset_elim in C; auto. destruct C as [C G].
           apply G; auto. 
Qed. 


Lemma lte_right_implies_minset_subset (X Y : finite_set S) (A : brel_lte_right (brel_minset rS lteS) bop_minset_union X Y = true) :
      brel_minset_subset rS lteS X Y = true. 
Proof. unfold brel_lte_right in A. unfold brel_minset_subset.
       unfold brel_minset in A. 
       apply brel_set_elim in A; auto. destruct A as [A B].
       assert (C := brel_subset_minset_union_left X Y). 
       exact (brel_subset_transitive S rS refS symS tranS _ _ _ C B).  
Qed. 
*) 

(* Think of (brel_minset_subset r) as an "optimization" of 
   brel_lte_right (brel_minsetset r) (bop_minset_union r) 

Lemma bop_minset_union_lub : bop_is_lub (brel_minset_subset rS lteS) bop_minset_union. 
Proof. intros X Y.
       destruct (bop_union_is_lub_wrt_lte_right X Y) as [A B].
       unfold is_upper_bound in A. destruct A as [A C].
       unfold is_lub. split. 
       - unfold is_upper_bound. split. 
         + unfold brel_minset_subset.
           apply lte_right_implies_minset_subset. exact A. 
         + unfold brel_minset_subset.
           apply lte_right_implies_minset_subset. exact C. 
       - intros U D. unfold is_upper_bound in D. destruct D as [D E]. 
         assert (G : is_upper_bound (brel_lte_right (brel_minset rS lteS) bop_minset_union) X Y U).
            unfold is_upper_bound. split.
              apply minset_subset_implies_lte_right. exact D. 
              apply minset_subset_implies_lte_right. exact E. 
         assert (F := B U G).
         apply lte_right_implies_minset_subset. exact F. 
Qed.
 *)

(*
Lemma bop_minset_union_glb : bop_is_glb (brel_dual (brel_minset_subset rS lteS)) bop_minset_union. 
Proof.  apply lub_implies_dual_glb. apply bop_minset_union_lub. Qed. 
*) 


End Theory.

Section ACAS.


Definition sg_CI_proofs_minset_union_from_po : 
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
let tot        := A_po_not_total S rS lteS poS in 
{|
  A_sg_CI_associative        := bop_minset_union_associative S rS refS symS tranS lteS lteCong lteRefl lteTran 
; A_sg_CI_congruence         := bop_minset_union_congruence S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_commutative        := bop_minset_union_commutative S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_idempotent         := bop_minset_union_idempotent S rS refS symS tranS lteS lteCong lteRefl lteTran
(*; A_sg_CI_selective_d        := bop_minset_union_selective_decide_v1 S rS refS symS tranS lteS lteCong lteRefl lteTran (inr tot) lteAntiSym *) 
; A_sg_CI_not_selective        := bop_minset_union_not_selective S rS refS symS tranS lteS lteCong lteRefl lteTran tot 
|}. 

(* Uhg!  huge duplication here ... change mostly "po" -> "qo"! *)
Definition sg_CI_proofs_minset_union_from_qo : 
  ∀ (S : Type) (rS lteS : brel S) (s : S) (f : S -> S) ,
     brel_not_trivial S rS f ->     
     eqv_proofs S rS -> qo_proofs S rS lteS -> 
        sg_CI_proofs (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS)
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
  A_sg_CI_associative        := bop_minset_union_associative S rS refS symS tranS lteS lteCong lteRefl lteTran 
; A_sg_CI_congruence         := bop_minset_union_congruence S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_commutative        := bop_minset_union_commutative S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_idempotent         := bop_minset_union_idempotent S rS refS symS tranS lteS lteCong lteRefl lteTran
(*; A_sg_CI_selective_d        := inr (brel_not_antisymmetric_implies_bop_minset_union_not_selective S rS refS symS tranS lteS lteCong lteRefl lteTran lteNotAntiSym) *) 
; A_sg_CI_not_selective        := brel_not_antisymmetric_implies_bop_minset_union_not_selective S rS refS symS tranS lteS lteCong lteRefl lteTran lteNotAntiSym
|}. 


Definition A_sg_minset_union_from_po_with_bottom (S : Type) (A : A_po_with_bottom S) : A_sg_BCI (finite_set S) := 
  let eqvS := A_po_wb_eqv S A in
  let botP := A_po_wb_exists_bottom S A in 
  let eqP  := A_eqv_proofs _ eqvS in
  let congS := A_eqv_congruence _ _ eqP in    
  let refS := A_eqv_reflexive _ _ eqP in
  let symS := A_eqv_symmetric _ _ eqP in
  let tranS := A_eqv_transitive _ _ eqP in
  let eq   := A_eqv_eq _ eqvS in  
  let s    := A_eqv_witness _ eqvS in
  let f    := A_eqv_new _ eqvS in
  let ntS  := A_eqv_not_trivial _ eqvS in
  let lteS := A_po_wb_lte _ A in
  let poP  := A_po_wb_proofs _ A in
  let lteCong    := A_po_congruence _ _ _ poP in
  let lteRefl    := A_po_reflexive _ _ _ poP in
  let lteTran    := A_po_transitive _ _ _ poP in
  let anti       := A_po_antisymmetric _ _ _ poP in
  {| 
     A_sg_BCI_eqv          := A_eqv_minset_from_or S (A_or_from_po_with_bottom A)
   ; A_sg_BCI_bop          := bop_minset_union S eq lteS
   ; A_sg_BCI_exists_id    := bop_minset_union_exists_id S eq refS symS tranS lteS lteCong lteRefl lteTran
   ; A_sg_BCI_exists_ann   := bop_minset_union_exists_ann_with_antisymmetry S eq refS symS tranS lteS lteCong lteRefl lteTran anti botP
   ; A_sg_BCI_proofs       := sg_CI_proofs_minset_union_from_po S eq lteS s f ntS eqP poP 
   ; A_sg_BCI_ast          := Ast_sg_minset_union (A_po_wb_ast S A)                                                                   
  |}.

Definition A_sg_minset_union_from_po_bounded (S : Type) (A : A_po_bounded S) : A_sg_BCI (finite_set S) := 
  let eqvS := A_po_bd_eqv S A in
  let botP := A_po_bd_exists_bottom S A in 
  let eqP  := A_eqv_proofs _ eqvS in
  let congS := A_eqv_congruence _ _ eqP in    
  let refS := A_eqv_reflexive _ _ eqP in
  let symS := A_eqv_symmetric _ _ eqP in
  let tranS := A_eqv_transitive _ _ eqP in
  let eq   := A_eqv_eq _ eqvS in  
  let s    := A_eqv_witness _ eqvS in
  let f    := A_eqv_new _ eqvS in
  let ntS  := A_eqv_not_trivial _ eqvS in
  let lteS := A_po_bd_lte _ A in
  let poP  := A_po_bd_proofs _ A in
  let lteCong    := A_po_congruence _ _ _ poP in
  let lteRefl    := A_po_reflexive _ _ _ poP in
  let lteTran    := A_po_transitive _ _ _ poP in
  let anti       := A_po_antisymmetric _ _ _ poP in
  {| 
     A_sg_BCI_eqv          := A_eqv_minset_from_or S (A_or_from_po_bounded A)
   ; A_sg_BCI_bop          := bop_minset_union S eq lteS
   ; A_sg_BCI_exists_id    := bop_minset_union_exists_id S eq refS symS tranS lteS lteCong lteRefl lteTran
   ; A_sg_BCI_exists_ann   := bop_minset_union_exists_ann_with_antisymmetry S eq refS symS tranS lteS lteCong lteRefl lteTran anti botP
   ; A_sg_BCI_proofs       := sg_CI_proofs_minset_union_from_po S eq lteS s f ntS eqP poP 
   ; A_sg_BCI_ast          := Ast_sg_minset_union (A_po_bd_ast S A)                                                                   
  |}.



Definition A_sg_minset_union_from_qo_with_bottom (S : Type) (A : A_qo_with_bottom S) : A_sg_BCI (finite_set S) := 
  let eqvS := A_qo_wb_eqv S A in
  let botP := A_qo_wb_exists_bottom S A in 
  let eqP  := A_eqv_proofs _ eqvS in
  let congS := A_eqv_congruence _ _ eqP in    
  let refS := A_eqv_reflexive _ _ eqP in
  let symS := A_eqv_symmetric _ _ eqP in
  let tranS := A_eqv_transitive _ _ eqP in
  let eq   := A_eqv_eq _ eqvS in  
  let s    := A_eqv_witness _ eqvS in
  let f    := A_eqv_new _ eqvS in
  let ntS  := A_eqv_not_trivial _ eqvS in
  let lteS := A_qo_wb_lte _ A in
  let poP  := A_qo_wb_proofs _ A in
  let lteCong    := A_qo_congruence _ _ _ poP in
  let lteRefl    := A_qo_reflexive _ _ _ poP in
  let lteTran    := A_qo_transitive _ _ _ poP in

  {| 
     A_sg_BCI_eqv          := A_eqv_minset_from_or S (A_or_from_qo_with_bottom A)
   ; A_sg_BCI_bop          := bop_minset_union S eq lteS
   ; A_sg_BCI_exists_id    := bop_minset_union_exists_id S eq refS symS tranS lteS lteCong lteRefl lteTran
   ; A_sg_BCI_exists_ann   := bop_minset_union_exists_ann_without_antisymmetry S eq refS symS tranS lteS lteCong lteRefl lteTran botP
   ; A_sg_BCI_proofs       := sg_CI_proofs_minset_union_from_qo S eq lteS s f ntS eqP poP 
   ; A_sg_BCI_ast          := Ast_sg_minset_union (A_qo_wb_ast S A)                                                                   
  |}.


Definition A_sg_minset_union_from_qo_bounded (S : Type) (A : A_qo_bounded S) : A_sg_BCI (finite_set S) := 
  let eqvS := A_qo_bd_eqv S A in
  let botP := A_qo_bd_exists_bottom S A in 
  let eqP  := A_eqv_proofs _ eqvS in
  let congS := A_eqv_congruence _ _ eqP in    
  let refS := A_eqv_reflexive _ _ eqP in
  let symS := A_eqv_symmetric _ _ eqP in
  let tranS := A_eqv_transitive _ _ eqP in
  let eq   := A_eqv_eq _ eqvS in  
  let s    := A_eqv_witness _ eqvS in
  let f    := A_eqv_new _ eqvS in
  let ntS  := A_eqv_not_trivial _ eqvS in
  let lteS := A_qo_bd_lte _ A in
  let poP  := A_qo_bd_proofs _ A in
  let lteCong    := A_qo_congruence _ _ _ poP in
  let lteRefl    := A_qo_reflexive _ _ _ poP in
  let lteTran    := A_qo_transitive _ _ _ poP in

  {| 
     A_sg_BCI_eqv          := A_eqv_minset_from_or S (A_or_from_qo_bounded A)
   ; A_sg_BCI_bop          := bop_minset_union S eq lteS
   ; A_sg_BCI_exists_id    := bop_minset_union_exists_id S eq refS symS tranS lteS lteCong lteRefl lteTran
   ; A_sg_BCI_exists_ann   := bop_minset_union_exists_ann_without_antisymmetry S eq refS symS tranS lteS lteCong lteRefl lteTran botP
   ; A_sg_BCI_proofs       := sg_CI_proofs_minset_union_from_qo S eq lteS s f ntS eqP poP 
   ; A_sg_BCI_ast          := Ast_sg_minset_union (A_qo_bd_ast S A)                                                                   
  |}.


End ACAS.

Section AMCAS.

Open Scope string_scope.   

Definition A_mcas_sg_minset_union_from_order {S : Type} (A : @A_or_mcas S) : A_sg_mcas (finite_set S) :=
match A with
| A_OR_Error sl         => A_MCAS_sg_Error _ sl
| A_OR_po_with_bottom B => A_sg_classify _ (A_MCAS_sg_BCI _ (A_sg_minset_union_from_po_with_bottom _ B))
| A_OR_po_bounded B     => A_sg_classify _ (A_MCAS_sg_BCI _ (A_sg_minset_union_from_po_bounded _ B))
| A_OR_qo_with_bottom B => A_sg_classify _ (A_MCAS_sg_BCI _ (A_sg_minset_union_from_qo_with_bottom _ B))
| A_OR_qo_bounded B     => A_sg_classify _ (A_MCAS_sg_BCI _ (A_sg_minset_union_from_qo_bounded _ B))
 (*****) 
| A_OR_to_with_bottom B => A_MCAS_sg_Error _ ("minset_union_from_order : there is no point in constructing minset union over a total order" :: nil)
| A_OR_to_bounded B     => A_MCAS_sg_Error _ ("minset_union_from_order : there is no point in constructing minset union over a total order" :: nil)
| A_OR_wo_with_bottom B => A_MCAS_sg_Error _ ("minset_union_from_order : there is no point in constructing minset union over a total order" :: nil)
| A_OR_wo_bounded  B    => A_MCAS_sg_Error _ ("minset_union_from_order : there is no point in constructing minset union over a total order" :: nil)
 (*****) 
| A_OR_or _          => A_MCAS_sg_Error _ ("Internal Error : mcas_sg_minset_union_from_or : the order is not classified!" :: nil)
 (*****)                                      
| A_OR_po _          => A_MCAS_sg_Error _ ("minset_union_from_order : order must have a bottom" :: nil)
| A_OR_po_with_top _ => A_MCAS_sg_Error _ ("minset_union_from_order : order must have a bottom" :: nil)
| A_OR_to _          => A_MCAS_sg_Error _ ("minset_union_from_order : order must have a bottom" :: nil)
| A_OR_to_with_top _ => A_MCAS_sg_Error _ ("minset_union_from_order : order must have a bottom" :: nil)
| A_OR_qo _          => A_MCAS_sg_Error _ ("minset_union_from_order : order must have a bottom" :: nil)
| A_OR_qo_with_top _ => A_MCAS_sg_Error _ ("minset_union_from_order : order must have a bottom" :: nil)
| A_OR_wo _          => A_MCAS_sg_Error _ ("minset_union_from_order : order must have a bottom" :: nil)
| A_OR_wo_with_top _ => A_MCAS_sg_Error _ ("minset_union_from_order : order must have a bottom" :: nil)
end.

End AMCAS.   

Section CAS.

(*  

Definition  check_minset_union_exists_ann {S : Type} (df_d : @check_bottoms_finite S) : @check_exists_ann (finite_set S)
  := match df_d with
     | Certify_Bottoms_Finite (f, _)  => Certify_Exists_Ann (f tt)
     | Certify_Is_Not_Bottoms_Finite => Certify_Not_Exists_Ann
     end.
*)
  
Definition assert_minset_union_not_selective {S : Type} (ntot : @assert_not_total S) : @assert_not_selective (finite_set S)
  := match ntot with
     | Assert_Not_Total (s, t) => Assert_Not_Selective (s :: nil, t :: nil)
     end.

Definition  assert_minset_union_not_selective_from_not_antisymmetric {S : Type} (nanti : @assert_not_antisymmetric S) : @assert_not_selective (finite_set S)
  := match nanti with
     | Assert_Not_Antisymmetric (s, t) => Assert_Not_Selective (s :: nil, t :: nil)
     end.

Definition sg_CI_certs_minset_union_from_po : ∀ {S : Type},  @po_certificates S -> @sg_CI_certificates (finite_set S)
:= λ {S} po,  
{|
  sg_CI_associative        := Assert_Associative  
; sg_CI_congruence         := Assert_Bop_Congruence  
; sg_CI_commutative        := Assert_Commutative  
; sg_CI_idempotent         := Assert_Idempotent  
(*; sg_CI_selective_d        := assert_minset_union_not_selective (po_not_total po) *) 
; sg_CI_not_selective      := assert_minset_union_not_selective (po_not_total po)
|}.

Definition sg_CI_certs_minset_union_from_qo : ∀ {S : Type},  @qo_certificates S -> @sg_CI_certificates (finite_set S)
:= λ {S} qo,  
{|
  sg_CI_associative        := Assert_Associative  
; sg_CI_congruence         := Assert_Bop_Congruence  
; sg_CI_commutative        := Assert_Commutative  
; sg_CI_idempotent         := Assert_Idempotent  
; sg_CI_not_selective        := assert_minset_union_not_selective_from_not_antisymmetric  (qo_not_antisymmetric qo)
|}. 


Definition sg_minset_union_from_po_with_bottom {S : Type} (A : @po_with_bottom S) : @sg_BCI (finite_set S) := 
  let eqvS := po_wb_eqv A   in
  let lteS := po_wb_lte A   in     
  let eq   := eqv_eq eqvS in  

   {| 
     sg_BCI_eqv           := eqv_minset_from_or (or_from_po_with_bottom A)
   ; sg_BCI_bop           := bop_minset_union S eq lteS 
   ; sg_BCI_exists_id     := Assert_Exists_Id nil 
   ; sg_BCI_exists_ann    := match po_wb_exists_bottom A with
                             | Assert_Exists_Bottom b => Assert_Exists_Ann (b :: nil)
                             end 
   ; sg_BCI_certs         := sg_CI_certs_minset_union_from_po (po_wb_certs A)
   ; sg_BCI_ast           := Ast_sg_minset_union (po_wb_ast A)                                                                   
   |}.

Definition sg_minset_union_from_po_bounded {S : Type} (A : @po_bounded S) : @sg_BCI (finite_set S) := 
  let eqvS := po_bd_eqv A   in
  let lteS := po_bd_lte A   in     
  let eq   := eqv_eq eqvS in  

   {| 
     sg_BCI_eqv           := eqv_minset_from_or (or_from_po_bounded A)
   ; sg_BCI_bop           := bop_minset_union S eq lteS 
   ; sg_BCI_exists_id     := Assert_Exists_Id nil 
   ; sg_BCI_exists_ann    := match po_bd_exists_bottom A with
                             | Assert_Exists_Bottom b => Assert_Exists_Ann (b :: nil)
                             end 
   ; sg_BCI_certs         := sg_CI_certs_minset_union_from_po (po_bd_certs A)
   ; sg_BCI_ast           := Ast_sg_minset_union (po_bd_ast A)                                                                   
   |}.

Definition sg_minset_union_from_qo_with_bottom {S : Type} (A : @qo_with_bottom S) : @sg_BCI (finite_set S) := 
  let eqvS := qo_wb_eqv A   in
  let eq   := eqv_eq eqvS in  
  let lteS := qo_wb_lte A   in   
   {| 
     sg_BCI_eqv           := eqv_minset_from_or (or_from_qo_with_bottom A)
   ; sg_BCI_bop           := bop_minset_union S eq lteS 
   ; sg_BCI_exists_id     := Assert_Exists_Id nil 
   ; sg_BCI_exists_ann    := match qo_wb_exists_bottom A with
                             | Assert_Exists_Qo_Bottom b => Assert_Exists_Ann (b :: nil)
                             end 
   ; sg_BCI_certs         := sg_CI_certs_minset_union_from_qo (qo_wb_certs A)
   ; sg_BCI_ast           := Ast_sg_minset_union (qo_wb_ast A)                                                                   
   |}.


Definition sg_minset_union_from_qo_bounded {S : Type} (A : @qo_bounded S) : @sg_BCI (finite_set S) := 
  let eqvS := qo_bd_eqv A   in
  let eq   := eqv_eq eqvS in  
  let lteS := qo_bd_lte A   in   
   {| 
     sg_BCI_eqv           := eqv_minset_from_or (or_from_qo_bounded A)
   ; sg_BCI_bop           := bop_minset_union S eq lteS 
   ; sg_BCI_exists_id     := Assert_Exists_Id nil 
   ; sg_BCI_exists_ann    := match qo_bd_exists_bottom A with
                             | Assert_Exists_Qo_Bottom b => Assert_Exists_Ann (b :: nil)
                             end 
   ; sg_BCI_certs         := sg_CI_certs_minset_union_from_qo (qo_bd_certs A)
   ; sg_BCI_ast           := Ast_sg_minset_union (qo_bd_ast A)                                                                   
   |}.


End CAS.

Section MCAS.

Open Scope string_scope.   

Definition mcas_sg_minset_union_from_order {S : Type} (A : @or_mcas S) : @sg_mcas (finite_set S) :=
match A with
| OR_Error sl         => MCAS_sg_Error sl
| OR_po_with_bottom B => sg_classify _ (MCAS_sg_BCI (sg_minset_union_from_po_with_bottom B))
| OR_po_bounded B     => sg_classify _ (MCAS_sg_BCI (sg_minset_union_from_po_bounded B))
| OR_qo_with_bottom B => sg_classify _ (MCAS_sg_BCI (sg_minset_union_from_qo_with_bottom B))
| OR_qo_bounded B     => sg_classify _ (MCAS_sg_BCI (sg_minset_union_from_qo_bounded B))
 (*****) 
| OR_to_with_bottom B => MCAS_sg_Error ("minset_union_from_order : there is no point in constructing minset union over a total order" :: nil)
| OR_to_bounded B     => MCAS_sg_Error ("minset_union_from_order : there is no point in constructing minset union over a total order" :: nil)
| OR_wo_with_bottom B => MCAS_sg_Error ("minset_union_from_order : there is no point in constructing minset union over a total order" :: nil)
| OR_wo_bounded  B    => MCAS_sg_Error ("minset_union_from_order : there is no point in constructing minset union over a total order" :: nil)
 (*****) 
| OR_or _          => MCAS_sg_Error ("Internal Error : mcas_sg_minset_union_from_or : the order is not classified!" :: nil)
 (*****)                                      
| OR_po _          => MCAS_sg_Error ("minset_union_from_order : order must have a bottom" :: nil)
| OR_po_with_top _ => MCAS_sg_Error ("minset_union_from_order : order must have a bottom" :: nil)
| OR_to _          => MCAS_sg_Error ("minset_union_from_order : order must have a bottom" :: nil)
| OR_to_with_top _ => MCAS_sg_Error ("minset_union_from_order : order must have a bottom" :: nil)
| OR_qo _          => MCAS_sg_Error ("minset_union_from_order : order must have a bottom" :: nil)
| OR_qo_with_top _ => MCAS_sg_Error ("minset_union_from_order : order must have a bottom" :: nil)
| OR_wo _          => MCAS_sg_Error ("minset_union_from_order : order must have a bottom" :: nil)
| OR_wo_with_top _ => MCAS_sg_Error ("minset_union_from_order : order must have a bottom" :: nil)
end.

End MCAS.   



Section Verify.

Lemma bop_minset_union_from_po_certs_correct 
      (S : Type) (eq lte : brel S) (s : S) (f : S -> S) (nt : brel_not_trivial S eq f) (eqv : eqv_proofs S eq) (po : po_proofs S eq lte) : 
      sg_CI_certs_minset_union_from_po (P2C_po eq lte po) 
      =                        
      P2C_sg_CI (finite_set S) (brel_minset eq lte) (bop_minset_union S eq lte)
                (sg_CI_proofs_minset_union_from_po S eq lte s f nt eqv po).
Proof. destruct eqv, po. 
       unfold sg_CI_certs_minset_union_from_po, sg_CI_proofs_minset_union_from_po, P2C_sg_CI, P2C_po; simpl.
       destruct A_po_not_total as [[a b] [L R]]; simpl; reflexivity. 
Qed. 

Lemma bop_minset_union_from_qo_certs_correct 
      (S : Type) (eq lte : brel S) (s : S) (f : S -> S) (nt : brel_not_trivial S eq f) (eqv : eqv_proofs S eq) (qo : qo_proofs S eq lte) : 
      sg_CI_certs_minset_union_from_qo (P2C_qo eq lte qo) 
      =                        
      P2C_sg_CI (finite_set S) (brel_minset eq lte) (bop_minset_union S eq lte)
                (sg_CI_proofs_minset_union_from_qo S eq lte s f nt eqv qo).
Proof. destruct eqv, qo. 
       unfold sg_CI_certs_minset_union_from_qo, sg_CI_proofs_minset_union_from_qo, P2C_sg_CI, P2C_qo; simpl.
       destruct A_qo_not_antisymmetric as [[c d] [[A B] C]]. simpl. 
       reflexivity. 
Qed. 
  


Theorem correct_minset_union_from_po_with_bottom (S : Type) (A : A_po_with_bottom S) : 
  sg_minset_union_from_po_with_bottom (A2C_po_with_bottom A)
  =
  A2C_sg_BCI (finite_set S) (A_sg_minset_union_from_po_with_bottom S A). 
Proof. unfold sg_minset_union_from_po_with_bottom, A_sg_minset_union_from_po_with_bottom, A2C_sg_BCI; simpl.
       rewrite <- bop_minset_union_from_po_certs_correct.       
       destruct A_po_wb_exists_bottom as [b P]. simpl. 
       unfold bop_minset_union_exists_ann_with_antisymmetry. 
       rewrite <- correct_eqv_minset_from_or.
       destruct A. unfold A2C_qo_with_bottom; simpl.
       unfold A_or_from_qo_with_bottom, or_from_qo_with_bottom, A2C_or; simpl. 
       reflexivity. 
Qed.

Theorem correct_minset_union_from_po_bounded (S : Type) (A : A_po_bounded S) : 
  sg_minset_union_from_po_bounded (A2C_po_bounded A)
  =
  A2C_sg_BCI (finite_set S) (A_sg_minset_union_from_po_bounded S A). 
Proof. unfold sg_minset_union_from_po_bounded, A_sg_minset_union_from_po_bounded, A2C_sg_BCI; simpl.
       rewrite <- bop_minset_union_from_po_certs_correct.       
       destruct A_po_bd_exists_bottom as [b P]. simpl. 
       unfold bop_minset_union_exists_ann_with_antisymmetry. 
       rewrite <- correct_eqv_minset_from_or.
       destruct A. unfold A2C_po_bounded; simpl.
       unfold A_or_from_po_bounded, or_from_po_bounded, A2C_or; simpl. 
       reflexivity. 
Qed.


Theorem correct_minset_union_from_qo_with_bottom (S : Type) (A : A_qo_with_bottom S) : 
  sg_minset_union_from_qo_with_bottom (A2C_qo_with_bottom A)
  =
  A2C_sg_BCI (finite_set S) (A_sg_minset_union_from_qo_with_bottom S A). 
Proof. unfold sg_minset_union_from_qo_with_bottom, A_sg_minset_union_from_qo_with_bottom, A2C_sg_BCI; simpl.
       rewrite <- bop_minset_union_from_qo_certs_correct.       
       destruct A_qo_wb_exists_bottom as [b [P Q]]. simpl. 
       rewrite <- correct_eqv_minset_from_or.
       destruct A. unfold A2C_qo_with_bottom; simpl.
       unfold A_or_from_qo_with_bottom, or_from_qo_with_bottom, A2C_or; simpl. 
       reflexivity. 
Qed.

Theorem correct_minset_union_from_qo_bounded (S : Type) (A : A_qo_bounded S) : 
  sg_minset_union_from_qo_bounded (A2C_qo_bounded A)
  =
  A2C_sg_BCI (finite_set S) (A_sg_minset_union_from_qo_bounded S A). 
Proof. unfold sg_minset_union_from_qo_bounded, A_sg_minset_union_from_qo_bounded, A2C_sg_BCI; simpl.
       rewrite <- bop_minset_union_from_qo_certs_correct.       
       destruct A_qo_bd_exists_bottom as [b [P Q]]. simpl. 
       rewrite <- correct_eqv_minset_from_or.
       destruct A. unfold A2C_qo_bounded; simpl.
       unfold A_or_from_qo_bounded, or_from_qo_bounded, A2C_or; simpl. 
       reflexivity. 
Qed.


Theorem correct_mcas_sg_minset_union_from_order (S : Type) (A : @A_or_mcas S): 
         mcas_sg_minset_union_from_order (A2C_mcas_or A)  
         = 
         A2C_mcas_sg _ (A_mcas_sg_minset_union_from_order A).
Proof. unfold mcas_sg_minset_union_from_order, A_mcas_sg_minset_union_from_order, A2C_mcas_sg; simpl.
       destruct A; unfold A2C_mcas_or; try reflexivity.
       rewrite correct_minset_union_from_po_with_bottom. reflexivity. 
       rewrite correct_minset_union_from_po_bounded. reflexivity.
       rewrite correct_minset_union_from_qo_with_bottom. reflexivity.        
       rewrite correct_minset_union_from_qo_bounded. reflexivity.        
Qed.  


End Verify.   
