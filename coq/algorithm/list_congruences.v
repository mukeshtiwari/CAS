From Coq Require Import
     List.
Import ListNotations.
From CAS Require Import
     coq.common.compute     
     coq.eqv.properties
     coq.eqv.nat
     coq.eqv.list
     coq.sg.and. 

Lemma map_congruence 
          (A B : Type)
          (eqA : brel A)
          (eqB : brel B)
          (f g : A → B)
          (cong : ∀ a a', eqA a a' = true -> eqB (f a) (g a') = true): 
      ∀ (l1 l2 : list A),  (brel_list eqA l1 l2 = true) -> brel_list eqB (map f l1) (map g l2) = true.
 Proof. induction l1. 
          + intros l2 I.  destruct l2. 
            ++ compute. reflexivity.
            ++ compute in I. congruence.
          + intros l2 I. destruct l2.
            ++ compute in I. congruence.
            ++ simpl.
               apply brel_list_cons_elim in I.
               destruct I as [I J]. 
               apply bop_and_intro; auto.
 Qed.                

Lemma fold_right_congruence 
          (A B : Type)
          (eqA : brel A)
          (eqB : brel B)
          (f g : B → A → A)
          (cong : ∀ b b' a a', eqB b b' = true -> eqA a a' = true -> eqA (f b a) (g b' a') = true): 
  ∀ (a a' : A) (l l' : list B),
    (eqA a a'= true) ->
      (brel_list eqB l l' = true) ->
        eqA (fold_right f a l) (fold_right g a' l') = true.
 Proof. intros a a'. induction l. 
          + intros l' I J.  destruct l'.
            ++ compute. exact I. 
            ++ compute in J. congruence.
          + intros l' I J. destruct l'.
            ++ compute in J. congruence.
            ++ simpl.
               apply brel_list_cons_elim in J.
               destruct J as [J K]. 
               assert (C := IHl l' I K).
               exact (cong _ _ _ _ J C). 
 Qed.                
