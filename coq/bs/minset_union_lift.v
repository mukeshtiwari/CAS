Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures.

Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.order. (* for below, equiv, ... *)

Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.minset_union.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.minset_lift.


Lemma os_left_strictly_monotone_implies_left_monotone (S : Type) (lte : brel S) (b : binary_op S):
  brel_reflexive S lte -> 
  os_left_strictly_monotone S lte b ->
  bop_congruence S (equiv lte) b ->
     os_left_monotone S lte b. 
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
  os_right_strictly_monotone S lte b ->
  bop_congruence S (equiv lte) b ->
     os_right_monotone S lte b. 
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




Lemma minset_union_lift_left_distributive_weak_TEST (anti: brel_antisymmetric S rS lteS)
  (NLM : os_not_left_monotone S lteS bS) :
     bop_not_left_distributive (finite_set S) (brel_set rS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS). 
Proof. unfold os_not_left_monotone in NLM.
       destruct NLM as [[a [b c]] [A B]].
       unfold bop_not_left_distributive. 
       exists (a :: nil, (b :: nil, c :: nil)).
       case_eq(brel_set rS ((a :: nil) <^> ((b :: nil) <U> (c :: nil)))  (((a :: nil) <^> (b :: nil)) <U> ((a :: nil) <^> (c :: nil)))); intro C; auto.
       apply brel_set_elim_prop in C; auto.  destruct C as [C D]. 
(*
     assume anti-symm 

      A : b <= c
      B : ab !<= ac 
      C: x in ms ({a} ms{b,c}} -> x in ms {ab, ac} 
      D: x in ms {ab, ac}      -> x in ms ({a} ms{b,c}} 

      case 1. c <= b. so c = b, and *** from B 
      case 2. c !<= b. 
      
       LHS : ms ({a} ms{b,c}} = ms ({a} {b}} = {ab} 
       RHS : ms {ab, ac} = {ac} if ac <= ab 
                         = {ac, ab} ow. 

       LHS <> RHS

         C': x in {ab} -> x in ms {ab, ac} 
         D': x in ms {ab, ac} -> x in {ab}
         claim : ac in ms {ab, ac}. 
            proof: if ac <= ab  so ac < ab 
                   then ms {ab, ac} = {ac} 
                   else ms {ab, ac} = {ab, ac} since ab # ac. 
         Now, from D' : ac = ab, this contradicts B. 
*) 
      case_eq(lteS c b); intro E. 
         admit. (* use anti-sym *)
         assert (G := D (bS a c)). 
         assert (H : bS a c [in] (((a :: nil) <^> (b :: nil)) <U> ((a :: nil) <^> (c :: nil)))). admit. 
         assert (I := G H). unfold bop_minset_lift in I. 
         apply in_minset_elim in I; auto. destruct I as [I J].
         apply in_set_bop_lift_elim in I; auto.
         destruct I as [x [y [[K L] M]]]. 
         admit. (* get ac = bc -> *** with B *)
Admitted.

              
Lemma minset_union_lift_left_distributive_weak
  (LM : os_left_monotone S lteS bS)
  (RM : os_right_monotone S lteS bS)       
  (DDD : (brel_antisymmetric S rS lteS) +  ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS))) : 
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
  (LM : os_left_monotone S lteS bS)
  (RM : os_right_monotone S lteS bS)             
  (DDD : (brel_antisymmetric S rS lteS) +  ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS))) :       
     bop_left_distributive (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS). 
Proof. intros X Y Z. apply set_equal_implies_minset_equal. apply minset_union_lift_left_distributive_weak; auto. Qed. 
       

Lemma minset_union_lift_right_distributive_weak
  (LM : os_left_monotone S lteS bS)      
  (RM : os_right_monotone S lteS bS)
  (DDD : (brel_antisymmetric S rS lteS) +  ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS))) :       
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
  (LM : os_left_monotone S lteS bS)            
  (RM : os_right_monotone S lteS bS)      
  (DDD : (brel_antisymmetric S rS lteS) +  ((os_left_strictly_monotone S lteS bS) * (os_right_strictly_monotone S lteS bS))) :   
     bop_right_distributive (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS). 
Proof. intros X Y Z. apply set_equal_implies_minset_equal. apply minset_union_lift_right_distributive_weak; auto. Qed. 
       



(*
Definition os_left_increasing (S : Type) (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, lte s (b s t) = true. 

 *)


Lemma lift_left_increasing 
      (inc : os_left_increasing S lteS bS) 
      (X Y : finite_set S):    
  (∀ (t : S), t [in] (X [^] Y) -> {x : S & (x [in] X) * (lteS x t = true)}).
Proof. intros t A.   unfold os_left_increasing in inc. 
       apply in_set_bop_lift_elim in A; auto. 
       destruct A as [x [y [[B C] D]]].
       exists x. split; auto. 
          rewrite (lteCong _ _ _ _ (refS x) D). exact (inc x y). 
Qed.        


Lemma lift_right_increasing 
      (inc : os_right_increasing S lteS bS) 
      (X Y : finite_set S):    
  (∀ (t : S), t [in] (Y [^] X) -> {x : S & (x [in] X) * (lteS x t = true)}).
Proof. intros t A.   
       apply in_set_bop_lift_elim in A; auto. 
       destruct A as [x [y [[B C] D]]].
       exists y. split; auto. 
          rewrite (lteCong _ _ _ _ (refS y) D). exact (inc y x). 
Qed.        


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


Lemma minset_union_lift_left_left_absorptive_increasing_weak
      (anti: brel_antisymmetric S rS lteS)
      (inc : os_left_increasing S lteS bS)       
      (X Y : finite_set S):    
      ([ms] X) [=S] ([ms] (X [U] (X [^] Y))).
Proof.  apply  union_left_antisymmetric; auto. apply lift_left_increasing; auto. Qed. 

Lemma minset_union_lift_left_right_absorptive_increasing_weak
      (anti: brel_antisymmetric S rS lteS)
      (inc : os_right_increasing S lteS bS)       
      (X Y : finite_set S):    
      ([ms] X) [=S] ([ms] (X [U] (Y [^] X))).
Proof.  apply  union_left_antisymmetric; auto. apply lift_right_increasing; auto. Qed. 

(* STRICT VERSIONS *)

Lemma lift_left_strictly_increasing 
      (sinc : os_left_strictly_increasing S lteS bS) 
      (X Y : finite_set S):    
  (∀ (t : S), t [in] (X [^] Y) -> {x : S & (x [in] X) * (below lteS t x = true)}).
Proof. intros t A.   unfold os_left_strictly_increasing in sinc. 
       apply in_set_bop_lift_elim in A; auto. 
       destruct A as [x [y [[B C] D]]].
       exists x. split; auto. 
          rewrite (below_congruence _ _ _ lteCong _ _ _ _ D (refS x)).
          destruct (sinc x y) as [E F]. apply below_intro; auto. 
Qed.        

Lemma lift_right_strictly_increasing 
      (sinc : os_right_strictly_increasing S lteS bS) 
      (X Y : finite_set S):    
  (∀ (t : S), t [in] (Y [^] X) -> {x : S & (x [in] X) * (below lteS t x = true)}).
Proof. intros t A.   
       apply in_set_bop_lift_elim in A; auto. 
       destruct A as [x [y [[B C] D]]].
       exists y. split; auto.
          rewrite (below_congruence _ _ _ lteCong _ _ _ _ D (refS y)).       
          destruct (sinc y x) as [E F]. apply below_intro; auto. 
Qed.        

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


Lemma minset_union_lift_left_left_absorptive_strictly_increasing_weak
      (sinc : os_left_strictly_increasing S lteS bS)       
      (X Y : finite_set S):    
        ([ms] X) [=S] ([ms] (X [U] (X [^] Y))).
Proof.  apply  union_left_without_antisymmetry; auto. apply lift_left_strictly_increasing; auto. Qed.       

Lemma minset_union_lift_left_right_absorptive_strictly_increasing_weak
      (sinc : os_right_strictly_increasing S lteS bS)       
      (X Y : finite_set S):    
      ([ms] X) [=S] ([ms] (X [U] (Y [^] X))).
Proof.  apply  union_left_without_antisymmetry; auto. apply lift_right_strictly_increasing; auto. Qed. 



(*   X [=MS] (X <U> (X <^> Y))  *) 
Lemma minset_union_lift_left_left_absorptive_increasing
      (anti: brel_antisymmetric S rS lteS)
      (inc : os_left_increasing S lteS bS) :
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
  (inc : os_right_increasing S lteS bS) :
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
      (sinc : os_left_strictly_increasing S lteS bS) :
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
  (sinc : os_right_strictly_increasing S lteS bS) :
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




Lemma minset_union_lift_plus_id_equals_times_ann : 
   bops_id_equals_ann (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS).
Proof. exists nil. split. 
       apply bop_minset_union_id_is_nil; auto. 
       apply bop_minset_lift_ann_is_nil; auto. 
Qed.

Lemma minset_union_lift_times_id_equals_plus_ann_with_antisymmetry
   (LM : os_left_monotone S lteS bS)
   (RM : os_right_monotone S lteS bS)       
   (anti : brel_antisymmetric S rS lteS) : 
   os_bottom_equals_id S rS lteS bS -> 
       bops_id_equals_ann (finite_set S) (brel_minset rS lteS) (bop_minset_lift S rS lteS bS) (bop_minset_union S rS lteS). 
Proof. intros [b [A B]]. exists (b :: nil). split.
       apply bop_minset_lift_id_is_bottom; auto. (*uses anti, LM and RM *)
       assert (A' := anti b).
       apply bop_minset_union_exists_ann_is_bottom; auto. 
Qed. 


Lemma minset_union_lift_times_id_equals_plus_ann_without_antisymmetry
   (LM : os_left_monotone S lteS bS)
   (RM : os_right_monotone S lteS bS)             
   (smono : os_left_strictly_monotone S lteS bS * os_right_strictly_monotone S lteS bS): 
   os_qo_bottom_equals_id S rS lteS bS ->   
       bops_id_equals_ann (finite_set S) (brel_minset rS lteS) (bop_minset_lift S rS lteS bS) (bop_minset_union S rS lteS). 
Proof. intros [b [[A B] C]]. exists (b :: nil). split. 
       apply bop_minset_lift_id_is_bottom; auto. (* uses smono , LM and RM *)
       apply bop_minset_union_exists_ann_is_bottom; auto. 
Qed. 


Lemma minset_union_lift_times_id_equals_plus_ann_with_monotonicity
   (LM : os_left_monotone S lteS bS)
   (RM : os_right_monotone S lteS bS)
   (EEE : ((brel_antisymmetric S rS lteS) * (os_bottom_equals_id S rS lteS bS)) +
          ((os_qo_bottom_equals_id S rS lteS bS) * 
           (os_left_strictly_monotone S lteS bS) *
           (os_right_strictly_monotone S lteS bS))) :      
       bops_id_equals_ann (finite_set S) (brel_minset rS lteS) (bop_minset_lift S rS lteS bS) (bop_minset_union S rS lteS). 
Proof. destruct EEE as [[anti po_bot] | [[qo_bot LSM] RSM] ].
       apply minset_union_lift_times_id_equals_plus_ann_with_antisymmetry; auto. 
       apply minset_union_lift_times_id_equals_plus_ann_without_antisymmetry; auto. 
Qed. 
       
End Theory.

Section ACAS.



(*
Definition minset_union_lift_semiring_proofs (S: Type) (eq lte : brel S) (times : binary_op S)
????????             
:= 
{|
  A_semiring_left_distributive        := minset_union_lift_left_distributive S eq refs symS trnS lte lteCong lteRefl lteTran times tCong LM (inl anti)
; A_semiring_right_distributive       := minset_union_lift_left_distributive S eq refs symS trnS lte lteCong lteRefl lteTran times tCong RM (inl anti)
; A_semiring_left_left_absorptive_d   := inl (minset_union_lift_left_left_absorptive_increasing S eq refs symS trnS lte lteCong lteRefl lteTran times (inl anti) LINC)
; A_semiring_left_right_absorptive_d  := inl (minset_union_lift_left_left_absorptive_increasing S eq refs symS trnS lte lteCong lteRefl lteTran times (inl anti) LRNC) 
|}.

*) 
  
  
(* 



Record semiring_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_semiring_left_distributive        : bop_left_distributive S eq plus times 
; A_semiring_right_distributive       : bop_right_distributive S eq plus times 
; A_semiring_left_left_absorptive_d   : bops_left_left_absorptive_decidable S eq plus times 
; A_semiring_left_right_absorptive_d  : bops_left_right_absorptive_decidable S eq plus times 
}.


Record bounded_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_bounded_plus_id_is_times_ann : bops_id_equals_ann S eq plus times 
; A_bounded_times_id_is_plus_ann : bops_id_equals_ann S eq times plus 
}.

Record A_dioid (S : Type) := {
  A_dioid_eqv           : A_eqv S 
; A_dioid_plus          : binary_op S 
; A_dioid_times         : binary_op S 
; A_dioid_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus
; A_dioid_times_proofs  : msg_proofs S   (A_eqv_eq S A_dioid_eqv) A_dioid_times
; A_dioid_id_ann_proofs : bounded_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus A_dioid_times
; A_dioid_proofs        : semiring_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus A_dioid_times
; A_dioid_ast           : cas_ast
}.




I need a strictly structure with (q0, sg) with 
   (bop_congruence S (equiv lteS) bS)
   (os_qo_bottom_equals_id S rS lteS bS) 
   (os_left_strictly_monotone S lteS bS) 
   (os_right_strictly_monotone S lteS bS)



*) 





End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.   
  