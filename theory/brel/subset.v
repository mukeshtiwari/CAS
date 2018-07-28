Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop.
Require Import CAS.code.bop.
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.facts.

Definition bProp_congruence (S : Type) (r : brel S) (P : bProp S) := ∀ (a b : S),  r a b = true -> P a = P b. 

Section InSet.
  Variable S: Type.
  Variable r : brel S.
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.
  
Lemma in_set_cons_intro  : ∀ (a b : S) (X : finite_set S),
    ((r a b = true) + (in_set r X b = true)) ->   in_set r (a :: X) b = true.
Proof. intros a b X [H | H]; unfold in_set; fold (@in_set S); apply orb_is_true_right; auto. Qed.        
       
Lemma in_set_cons_elim : ∀ (a b : S) (X : finite_set S),
    in_set r (a :: X) b = true -> ((r a b = true) + (in_set r X b = true)). 
Proof. intros a b X H.
       unfold in_set in H. fold (@in_set S) in H. 
       apply orb_is_true_left in H.
       destruct H as [H | H]; auto.
Qed.        

Lemma in_set_right_congruence : ∀ (a b : S) (X : finite_set S),
    r a b = true -> in_set r X a = true -> in_set r X b = true.
Proof. intros a b X H.
       induction X.
       compute. auto.
       unfold in_set. fold (@in_set S).
       intro K.
       apply orb_is_true_right. apply orb_is_true_left in K.
       destruct K as [K | K].
       left. apply symS in H. apply (tranS _ _ _ H K). 
       right. apply IHX; auto.
Qed.

Lemma in_set_bProp_congruence : ∀ (X : finite_set S), bProp_congruence S r (in_set r X).
Proof. intros X a b E.
       case_eq(in_set r X a); intro H1; case_eq(in_set r X b); intro H2; auto. 
       rewrite (in_set_right_congruence _ _ _ E H1) in H2. discriminate H2. 
       apply symS in E. rewrite (in_set_right_congruence _ _ _ E H2) in H1. discriminate H1. 
Qed.

Lemma in_set_filter_elim :    ∀ (g : bProp S) (X : finite_set S) (a : S),
    bProp_congruence S r g ->
    in_set r (filter g X) a = true -> (g a = true) * (in_set r X a = true).
Proof. intros g X a cong H.
       induction X.  compute in H.  discriminate H.
       unfold filter in H. fold (@filter S) in H. 
       unfold in_set.  fold (@in_set S).
       case_eq(g a); intro J; case_eq(r a a0); intro K; case_eq(g a0); intro L; auto. 
       split; auto. simpl. rewrite L in H. unfold in_set in H. fold (@in_set S) in H. 
       rewrite K in H. simpl in H.  apply IHX; auto. 
       split; auto; simpl. rewrite L in H. apply IHX; auto.
       rewrite (cong _ _ K) in J. rewrite L in J. discriminate J.
       rewrite L in H. destruct (IHX H) as [F _]. rewrite F in J. discriminate J. 
       rewrite L in H.
       unfold in_set in H. fold (@in_set S) in H. rewrite K in H. simpl in H. 
       destruct (IHX H) as [F _]. rewrite F in J. discriminate J.
       rewrite L in H. destruct (IHX H) as [F _]. rewrite F in J. discriminate J.
Qed.

Lemma in_set_filter_intro :    ∀ (g : bProp S) (X : finite_set S) (a : S),
    bProp_congruence S r g ->
    (g a = true) * (in_set r X a = true) -> in_set r (filter g X) a = true.
Proof. intros g X a cong [gP inX].
       induction X.
       compute in inX.  discriminate inX. 
       unfold in_set in inX. fold (@in_set S) in inX.
       unfold filter. fold (@filter S).
       apply orb_is_true_left in inX.
       destruct inX as [inX | inX].
       assert (H := cong _ _ inX).  rewrite gP in H. 
       rewrite <- H. unfold in_set. fold (@in_set S). rewrite inX. simpl. reflexivity.
       case_eq(g a0); intro H.
       apply in_set_cons_intro; auto. 
       apply IHX; auto.        
Qed. 

       (* ********************* *) 

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
         apply (in_set_right_congruence a a0 w Q H1).
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

End InSet. 