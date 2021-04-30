

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.

Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset.
Require Import CAS.coq.theory.order. (* for below, equiv, ... *) 
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



Definition bop_minset_union : binary_op (finite_set S)
  := λ X Y, uop_minset lteS (bop_union rS (uop_minset lteS X) (uop_minset lteS Y)). 



Notation "a [=] b"  := (rS a b = true)          (at level 15).
Notation "a [<>] b" := (rS a b = false)         (at level 15).
Notation "a <<= b"  := (lteS a b = true)        (at level 15).
Notation "a !<<= b" := (lteS a b = false)       (at level 15).

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

Lemma bop_minset_union_congruence : bop_congruence (finite_set S) (brel_minset rS lteS) bop_minset_union.
Proof. unfold bop_congruence. intros X1 X2 Y1 Y2 A B.
       unfold bop_minset_union.
       unfold brel_minset in A, B. 
       assert (C := bop_union_congruence _ _ _ _ A B).
       assert (D := uop_minset_congruence_weak _ _ C).
       unfold brel_minset. 
       apply uop_minset_congruence_weak; auto. 
Qed.

Lemma minset_union_commutative_weak (X Y : finite_set S) : ([ms] (X [U] Y)) [=MS] ([ms] (Y [U] X)). 
Proof. assert (A : (X [U] Y) [=S] (Y [U] X)).
          apply bop_union_commutative; auto. 
       assert (B := uop_minset_congruence_weak _ _ A).
       apply uop_minset_congruence_weak; auto.
Qed. 

Lemma bop_minset_union_commutative : bop_commutative (finite_set S) (brel_minset rS lteS) bop_minset_union.
Proof. intros X Y. unfold bop_minset_union. apply minset_union_commutative_weak. Qed. 


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
       assert (A := bop_union_nil S rS refS symS tranS ([ms] X)).
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


Lemma bop_minset_union_exists_ann_is_bottom (b : S) :
     brel_is_bottom S lteS b -> (∀ t : S, b <<= t → t <<= b → b [=] t) ->  
     bop_is_ann (finite_set S) (brel_minset rS lteS) bop_minset_union (b :: nil). 
Proof. intros A A'. unfold brel_is_bottom in A.  unfold bop_is_ann. intro X.
          assert (B : ([ms] (b :: X)) [=MS] (b :: nil)).
             exact (minset_bottom_aux _ _ refS symS tranS lteS lteCong lteRefl lteTrans X  b A A'). 
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
Proof. intros [b [A A']]. exists (b :: nil). apply (bop_minset_union_exists_ann_is_bottom b); auto. Qed. 



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
Qed.              


Lemma bop_minset_union_not_selective : (brel_not_total S lteS) → bop_not_selective (finite_set S) (brel_minset rS lteS) bop_minset_union. 
Proof. intros [ [s t] [L R] ]. 
       exists (s :: nil, t :: nil). split. 
       unfold bop_minset_union.
       unfold brel_minset. 
       rewrite minset_singleton. rewrite minset_singleton. 
       case_eq(brel_set rS ([ms] ([ms] ((s :: nil) [U] (t :: nil)))) (s :: nil) ); intro A; auto. 
       (* need s [#] t -> [ms] ((s :: nil) [U] (t :: nil)) [=S] (s :: t :: nil)   *) 
Admitted.



Lemma total_implies_singlton_minsets (tot : brel_total S lteS) (X : finite_set S):  (nil [=S] X) + {s : S & (s :: nil) [=S] [ms] X}.
Admitted.  


Lemma bop_minset_union_selective_weak (tot : brel_total S lteS) (anti : brel_antisymmetric S rS lteS) (X Y : finite_set S):
  (X <U> Y) [=S] X + (X <U> Y) [=S] Y. 
Proof. destruct(total_implies_singlton_minsets tot X) as [A | A];
       destruct(total_implies_singlton_minsets tot Y) as [B | B].
          admit.        
          right. admit. 
          left.  admit.           
          destruct A as [x A]. destruct B as [y B]. 
          case_eq(lteS x y); intro C;  case_eq(lteS y x); intro D.  
            (* x ~ y *)  assert (E := anti _ _ C D). left. admit. 
            (* x < y *)  left. admit.
            (* y < x *)  right. admit.
            (* x # y *)  destruct (tot x y) as [E | E]. rewrite E in C. discriminate C. rewrite E in D. discriminate D. 
Admitted. 
          
Lemma bop_minset_union_selective (tot : brel_total S lteS) (anti : brel_antisymmetric S rS lteS) :
  bop_selective (finite_set S) (brel_minset rS lteS) bop_minset_union. 
Proof. intros X Y.
       destruct (bop_minset_union_selective_weak tot anti X Y) as [B | B]. 
       left. apply set_equal_implies_minset_equal; auto.
       right. apply set_equal_implies_minset_equal; auto.        
Qed. 

Definition bop_minset_union_selective_decide (tot_d : brel_total_decidable S lteS) (anti : brel_antisymmetric S rS lteS): 
      bop_selective_decidable (finite_set S) (brel_minset rS lteS) bop_minset_union
 := match tot_d with
     | inl tot  => inl (bop_minset_union_selective tot anti) 
     | inr ntot => inr (bop_minset_union_not_selective ntot)
    end.


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
; A_sg_CI_selective_d        := bop_minset_union_selective_decide S rS s f ntS congS refS symS tranS lteS lteCong lteRefl lteTran (inr tot) lteAntiSym
|}. 




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
; A_sg_CI_selective_d        := inr (brel_not_antisymmetric_implies_bop_minset_union_not_selective S rS refS symS tranS lteS lteCong lteRefl lteTran lteNotAntiSym)
|}. 



(*
Definition A_sg_CI_minset_union : ∀ (S : Type),  A_qo_with_bottom S -> A_sg_CI (finite_set S)
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
   ; A_sg_CI_bop          := bop_minset_union S eq lteS
   ; A_sg_CI_exists_id_d  := inl (bop_minset_union_exists_id S eq congS refS symS tranS lteS lteCong lteRefl)
   ; A_sg_CI_exists_ann_d := inl (bop_minset_union_exists_ann S eq f ntS congS refS symS tranS lteS lteCong lteRefl lteTran botP)
   ; A_sg_CI_proofs       := sg_CI_proofs_minset_union_from_qo S eq lteS s f ntS eqP poP 
   ; A_sg_CI_ast          := Ast_sg_minset_union (A_po_ast S qo)                                                                   
  |}.

*) 

(*

from po:   with bottom? 

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




Why needed? 

    3) sg_CI_with_ann 
*) 


End ACAS.


(*
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
 *)

(*
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
  

*) 