Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop.
Require Import CAS.code.bop.
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts.
Require Import CAS.theory.brel2_in_set.

Lemma brel_subset_intro : ∀ (S : Type) (r : brel S), 
     brel_reflexive S r ->
     brel_symmetric S r -> 
     brel_transitive S r -> 
        ∀ (x w : finite_set S), 
          (∀ a:S, in_set S r x a = true -> in_set S r w a = true) 
               -> brel_subset S r x w = true. 
Proof. intros S r refS symS transS. induction x; intros w H; unfold brel_subset.  
       reflexivity. 
       fold brel_subset. rewrite (H a). simpl. 
       apply IHx.  intros t Q. apply H. unfold in_set. fold in_set. 
          rewrite Q. apply orb_comm. unfold in_set. fold in_set. 
          rewrite (refS a). simpl. reflexivity. 
Defined. 


Lemma brel_subset_elim : ∀ (S : Type) (r : brel S), 
       brel_symmetric S r -> brel_transitive S r -> 
           ∀ (x w : finite_set S), 
               brel_subset S r x w = true -> 
                   ∀ a:S, in_set S r x a = true -> in_set S r w a = true. 
Proof. intros S r symS transS. induction x. 
       intros w H a Q. unfold in_set in Q. discriminate. 
       intros w H a0 Q.              
       unfold brel_subset in H.  fold brel_subset in H. 
       apply andb_is_true_left in H. destruct H as [H1 H2].
       unfold in_set in Q. fold in_set in Q.  
       apply orb_is_true_left in Q. destruct Q as [Q|Q]. 
         apply symS in Q.
         apply (in_set_right_congruence S r symS transS w a a0 Q H1). 
         apply (IHx w H2 a0 Q). 
Defined. 

Lemma brel_subset_filter_intro : 
   ∀ (S : Type) (r : brel S) (f g : bProp S),
       brel_reflexive S r →
       brel_symmetric S r →
       brel_transitive S r →
       bProp_congruence S r f →
       bProp_congruence S r g →
      (∀ s : S, g s = true -> f s = true) -> (* <<< NB *) 
        ∀ (X Y : finite_set S), brel_subset S r X Y = true -> 
            brel_subset S r (filter g X) (filter f Y) = true. 
Proof. intros S r f g refS symS transS cong_f cong_g P X Y H.
       apply brel_subset_intro; auto. 
       assert(A := brel_subset_elim S r symS transS _ _ H). 
       intros a J. apply in_set_filter_elim in J; auto. destruct J as [L R].
       apply in_set_filter_intro; auto. 
Defined. 


Lemma brel_subset_uop_filter_intro : 
   ∀ (S : Type) (r : brel S) (f g : bProp S),
       brel_reflexive S r →
       brel_symmetric S r →
       brel_transitive S r →
       bProp_congruence S r f →
       bProp_congruence S r g →
      (∀ s : S, g s = true -> f s = true) -> 
        ∀ (X Y : finite_set S), brel_subset S r X Y = true -> 
            brel_subset S r (uop_filter S g X) (uop_filter S f Y) = true. 
Proof. unfold uop_filter. apply brel_subset_filter_intro; auto. Defined. 



(*****************)

Lemma brel_subset_reflexive : ∀ (S : Type) (r : brel S), 
         brel_reflexive S r → 
          brel_symmetric S r → 
          brel_transitive S r → 
           brel_reflexive (finite_set S) (brel_subset S r). 
Proof. unfold brel_reflexive. intros S r refS symS transS. induction s. 
       simpl. reflexivity. 
       unfold brel_subset. fold brel_subset. unfold in_set. rewrite (refS a). simpl.
       apply brel_subset_intro; auto.   
       intros b H. apply in_set_cons_intro; auto. 
Defined. 

(* 
Lemma brel_subset_not_trivial : ∀ (S : Type) (r : brel S), 
              (brel_not_trivial _ r) → brel_not_trivial (finite_set S) (brel_subset S r). 
Proof. unfold brel_not_trivial. 
       intros S r [s [ t P] ]. 
       exists (s :: nil). exists (t :: nil). simpl. unfold brel_set. 
       unfold brel_subset. unfold brel_and_sym. unfold in_set. rewrite P. simpl. reflexivity. 
Defined. 
*) 

Lemma brel_subset_transitive : ∀ (S : Type) (r : brel S), 
        (brel_reflexive _ r) → (brel_symmetric _ r) → (brel_transitive _ r) → 
              brel_transitive (finite_set S) (brel_subset S r). 
Proof. intros S r refS symS transS x y z H1 H2. 
      assert (Q1 := brel_subset_elim S r symS transS x y H1). 
      assert (Q2 := brel_subset_elim S r symS transS y z H2). 
      apply (brel_subset_intro S r refS symS transS). 
      intros a I. apply Q2. apply Q1. assumption. 
Defined. 

Lemma brel_subset_antisymmetric : ∀ (S : Type) (r : brel S), 
        (brel_reflexive _ r) → (brel_symmetric _ r) → (brel_transitive _ r) → 
              brel_antisymmetric (finite_set S) (brel_set S r) (brel_subset S r). 
Proof. intros S r refS symS transS x y H1 H2. 
       unfold brel_set. unfold brel_and_sym. rewrite H1, H2. auto. 
Defined. 

