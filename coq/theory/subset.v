Require Import Coq.Bool.Bool. 
Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set.

Section SubSet.
  Variable S: Type.
  Variable r : brel S.
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.
  
Lemma brel_subset_intro : 
        ∀ (x w : finite_set S), 
          (∀ a:S, in_set r x a = true -> in_set r w a = true) 
               -> brel_subset r x w = true. 
Proof. induction x; intros w H; unfold brel_subset.  
       reflexivity. 
       fold (@brel_subset S). rewrite (H a). simpl. 
       apply IHx.  intros t Q. apply H. unfold in_set. fold (@in_set S). 
          rewrite Q. apply orb_comm. unfold in_set. fold (@in_set S). 
          rewrite (refS a). simpl. reflexivity. 
Defined. 


Lemma brel_subset_elim : 
           ∀ (x w : finite_set S), 
               brel_subset r x w = true -> 
                   ∀ a:S, in_set r x a = true -> in_set r w a = true. 
Proof. induction x. 
       intros w H a Q. unfold in_set in Q. discriminate. 
       intros w H a0 Q.              
       unfold brel_subset in H.  fold (@brel_subset S) in H. 
       apply andb_is_true_left in H. destruct H as [H1 H2].
       unfold in_set in Q. fold (@in_set S) in Q.  
       apply orb_is_true_left in Q. destruct Q as [Q|Q]. 
         apply symS in Q.  
         apply (in_set_right_congruence S r symS tranS a a0 w Q H1).
         apply (IHx w H2 a0 Q). 
Qed. 


Lemma brel_subset_filter_intro : 
   ∀ (f g : bProp S),
       bProp_congruence S r f →
       bProp_congruence S r g →
      (∀ s : S, g s = true -> f s = true) -> (* <<< NB *) 
        ∀ (X Y : finite_set S), brel_subset r X Y = true -> 
            brel_subset r (filter g X) (filter f Y) = true. 
Proof. intros f g cong_f cong_g P X Y H.
       apply brel_subset_intro; auto. 
       assert(A := brel_subset_elim _ _ H). 
       intros a J.
       apply in_set_filter_elim in J; auto.
       destruct J as [L R].
       apply in_set_filter_intro; auto. 
Defined.


Lemma brel_subset_uop_filter_intro : 
   ∀ (f g : bProp S),
       bProp_congruence S r f →
       bProp_congruence S r g →
      (∀ s : S, g s = true -> f s = true) -> 
        ∀ (X Y : finite_set S), brel_subset r X Y = true -> 
            brel_subset r (uop_filter g X) (uop_filter f Y) = true. 
Proof. unfold uop_filter. apply brel_subset_filter_intro; auto. Defined. 



(*****************)

Lemma brel_subset_reflexive : brel_reflexive (finite_set S) (brel_subset r). 
Proof. unfold brel_reflexive. induction s. 
       simpl. reflexivity. 
       unfold brel_subset. fold (@brel_subset S). unfold in_set. rewrite (refS a). simpl.
       apply brel_subset_intro; auto.   
       intros b H. apply in_set_cons_intro; auto. 
Defined. 

Lemma brel_subset_transitive : brel_transitive (finite_set S) (brel_subset r). 
Proof. intros x y z H1 H2. 
      assert (Q1 := brel_subset_elim x y H1). 
      assert (Q2 := brel_subset_elim y z H2). 
      apply brel_subset_intro. 
      intros a I. apply Q2. apply Q1. assumption. 
Defined. 

Lemma brel_subset_antisymmetric : brel_antisymmetric (finite_set S) (brel_set r) (brel_subset r). 
Proof. intros x y H1 H2. unfold brel_set. unfold brel_and_sym. rewrite H1, H2. auto.  Defined. 

End SubSet. 