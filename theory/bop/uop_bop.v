Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.uop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.brel.and_sym. 
Require Import CAS.theory.bop.then_unary. 
Require Import CAS.theory.bop.intersect. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.in_set.
Require Import CAS.theory.brel.subset.
Require Import CAS.theory.brel.set.
Require Import CAS.theory.uop.duplicate_elim. 
Require Import CAS.theory.bop.union. 

Section Lift. 

Variable S  : Type. 
Variable rS : brel S. 
Variable bS : binary_op S. 

Variable refS  : brel_reflexive S rS.    
Variable tranS : brel_transitive S rS. 
Variable symS  : brel_symmetric S rS. 

Variable assS : bop_associative S rS bS. 

Open Scope list_scope.

Definition ltran_list_product : left_transform S (list S) 
:= fix f a y := 
      match y with
         | nil => nil 
         | b :: rest => (bS a b ) :: (f a rest)
      end.

Definition aux_list_product : (list S) -> (list S) -> (list S) -> list S
:= fix f x y acc := 
      match x with
         | nil => acc 
         | a :: rest => f rest y ((ltran_list_product a y) ++ acc)
      end.

Definition bop_list_product : binary_op(list S) := λ x y, aux_list_product x y nil. 

Definition bop_lift : binary_op(finite_set S) := 
    λ x y, uop_duplicate_elim S rS (bop_list_product x y). 


(* MOVE *) 
Lemma brel_set_intro_false : ∀ (X Y : finite_set S), 
     {s : S & (in_set S rS X s = true) * (in_set S rS Y s = false)} → brel_set S rS X Y = false. 
Proof. intros X Y [ s [T F]]. 
       case_eq(brel_set S rS X Y); intro H. 
          apply brel_set_elim in H. destruct H as [L R]. 
          assert (K := brel_subset_elim S rS symS tranS X Y L s T). 
          rewrite K in F. discriminate. 
          reflexivity. 
Defined. 

Lemma  in_set_bop_lift_elim :
 ∀ (X Y : finite_set S),  ∀ (a : S), 
  in_set S rS (bop_lift X Y) a = true -> 
   {x : S & {y : S & (in_set S rS X x = true) * (in_set S rS Y y = true) * (rS a (bS x y) = true)}}.
Proof. intros. 
       unfold bop_lift in H.        
       rewrite in_set_duplicate_elim in H. 
       unfold bop_list_product in H. 
       induction X. 
          compute in H. discriminate. 
          unfold aux_list_product in H.           
          fold aux_list_product in H.           
          admit. 
Defined. 

Lemma  in_set_bop_lift_intro :
   ∀ (X Y : finite_set S),  ∀ (a x y : S), 
        in_set S rS X x = true -> 
        in_set S rS Y y = true -> 
           in_set S rS (bop_lift X Y) (bS x y) = true. 
Proof. intros. 
       unfold bop_lift. 
       rewrite in_set_duplicate_elim. 
       induction X. 
          compute in H. discriminate. 
          apply in_set_cons_elim in H. 
          destruct H as [H | H].
             unfold bop_list_product. 
             induction Y. 
                compute in H0. discriminate. 
                apply in_set_cons_elim in H0. 
                destruct H0 as [H0 | H0].
                unfold aux_list_product. fold aux_list_product. 
                unfold ltran_list_product. fold ltran_list_product. 
                admit. 
          admit. 
  admit .
Qed. 


Lemma  lift_lemma_1 : 
   ∀ (s t u : finite_set S) (a : S),
   in_set S rS (bop_lift (bop_lift s t) u) a = true
   → in_set S rS (bop_lift s (bop_lift t u)) a = true. 
Proof. intros. 
       apply in_set_bop_lift_elim in H. 
       destruct H as [x [y [[H J] K]]].
       apply in_set_bop_lift_elim in H. 
       destruct H as [x0 [y0 [[H J0] K0]]].

       apply in_set_bop_lift_intro. 

Hypothesis  lift_lemma_2 : 
   ∀ (s t u : finite_set S) (a : S),
   in_set S rS (bop_lift s (bop_lift t u)) a = true
    → in_set S rS (bop_lift (bop_lift s t) u) a = true. 

Lemma bop_lift_associative : bop_associative (finite_set S) (brel_set S rS) bop_lift. 
Proof. unfold bop_associative. intros s t u. 
       apply brel_set_intro. 
       split; apply brel_subset_intro; auto. 
Qed. 


Hypothesis  lift_lemma_3 : 
   ∀ (s1 s2 t1 t2 : finite_set S),  
     (brel_subset S rS s1 t1 = true) ->  
     (brel_subset S rS s2 t2 = true) ->  
   ∀ a : S,
   in_set S rS (bop_lift s1 s2) a = true
   → in_set S rS (bop_lift t1 t2) a = true. 


Lemma bop_lift_congruence : bop_congruence (finite_set S) (brel_set S rS) bop_lift. 
Proof. unfold bop_congruence. intros s1 s2 t1 t2 H1 H2. 
       apply brel_set_elim in H1. apply brel_set_elim in H2. 
       destruct H1 as [L1 R1]. destruct H2 as [L2 R2]. 
       apply brel_set_intro. 
       split; apply brel_subset_intro; auto. 
          apply lift_lemma_3; auto.  
          apply lift_lemma_3; auto.  
Qed. 



Hypothesis  lift_lemma_4 : 
  bop_commutative S rS bS ->  
   ∀ (X Y : finite_set S), 
      ∀ a : S, in_set S rS (bop_lift X Y) a = true → in_set S rS (bop_lift Y X) a = true. 
(*
Proof. intros commS X Y a H. 
       apply in_set_bop_lift_elim in H as [x [ y [[xP yP] eqP]]].
       apply (in_set_bop_lift_intro _ _ a y x yP xP). 
Qed. 
*)
 
Lemma bop_lift_commutative : 
     bop_commutative S rS bS -> bop_commutative (finite_set S) (brel_set S rS) bop_lift. 
Proof. unfold bop_commutative. intros commS s t. 
       apply brel_set_intro. 
       split; apply brel_subset_intro; auto. 
Qed. 












(* Martelli semiring is not idempotent! *) 
Lemma bop_lift_not_idempotent : 
    bop_not_selective S rS bS -> 
    bop_not_idempotent (finite_set S) (brel_set S rS) bop_lift. 
Proof. intros [[a b] [L R]]. exists (a :: b :: nil). 
       unfold bop_lift. unfold bop_list_product. unfold aux_list_product. 
       unfold ltran_list_product. unfold app. 
       apply brel_set_intro_false. 
       exists (bS a b). split. 
          rewrite in_set_duplicate_elim. compute.
          rewrite (refS (bS a b)). 
          case(rS (bS a b) (bS b a)); 
          case(rS (bS a b) (bS b b)); 
          case(rS (bS a b) (bS a a)); reflexivity. 
          compute. rewrite L, R. reflexivity. 
Defined. 

(* 
Selective -> Idempotent 
not Idempotent -> not Selective

Don't really need this. 
*) 
Lemma bop_lift_not_idempotent_v2 : 
    bop_not_idempotent S rS bS -> 
    bop_not_idempotent (finite_set S) (brel_set S rS) bop_lift. 
Proof. intros [a NP]. exists (a :: nil). 
       unfold bop_lift. unfold bop_list_product. unfold aux_list_product. 
       unfold ltran_list_product. unfold app. 
       apply brel_set_intro_false. 
       exists (bS a a); compute. split. 
          rewrite (refS (bS a a)). reflexivity. 
          rewrite NP. reflexivity. 
Defined. 

Lemma bop_lift_idempotent : 
    bop_selective S rS bS -> 
    bop_idempotent (finite_set S) (brel_set S rS) bop_lift. 
Proof. intros selS X. 
       apply brel_set_intro. split. 
       induction X. 
          compute. reflexivity. 
          admit. 
       admit. 
Qed. 



End Lift. 