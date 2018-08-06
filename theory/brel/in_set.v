Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 
Require Import CAS.code.bop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.facts.

(***********************************)

(* move ? *) 
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

Lemma in_set_uop_filter_elim : ∀ (f : bProp S) (X : finite_set S) (a : S), (bProp_congruence S r f) -> 
           in_set r (uop_filter f X) a = true -> (f a = true) * (in_set r X a = true).
Proof. unfold uop_filter. apply in_set_filter_elim. Defined. 


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


Lemma in_set_uop_filter_intro :    ∀ (f : bProp S) (X : finite_set S) (a : S),(bProp_congruence S r f) -> 
          (f a = true) * (in_set r X a = true) -> in_set r (uop_filter f X) a = true. 
Proof. unfold uop_filter. apply in_set_filter_intro. Defined. 


Lemma in_set_concat_intro : ∀ (X Y : finite_set S) (a : S),
     (in_set r X a = true) + (in_set r Y a = true) → in_set r (X ++ Y) a = true. 
Proof. induction X. intros Y a [L | R]. 
             compute in L. discriminate L. 
             rewrite List.app_nil_l. exact R. 
          intros Y a0 [L | R]. 
             rewrite <- List.app_comm_cons. 
             unfold in_set. fold (@in_set S). unfold in_set in L. fold (@in_set S) in L. 
             apply orb_is_true_left in L. destruct L as [L | L]. 
                rewrite L. simpl. reflexivity. 
                apply orb_is_true_right. right. apply IHX. left. exact L. 

             rewrite <- List.app_comm_cons. 
             unfold in_set. fold (@in_set S). 
             apply orb_is_true_right. right. apply IHX. right. exact R. 
Defined. 

Lemma in_set_concat_elim : ∀ (X Y : finite_set S) (a : S),
      in_set r (X ++ Y) a = true → (in_set r X a = true) + (in_set r Y a = true). 
Proof. induction X. 
          intros U a H. rewrite List.app_nil_l in H. right. exact H. 
          intros U b H. rewrite <- List.app_comm_cons in H. 
          unfold in_set in H. fold (@in_set S) in H. 
          apply orb_is_true_left in H.  destruct H as [L | R]. 
             left. unfold in_set. fold (@in_set S). rewrite L. simpl. reflexivity. 
             assert (K := IHX U b R). destruct K as [KL | KR].
                left. apply in_set_cons_intro. right. exact KL. 
                right. exact KR. 
Defined. 

(* 
Hypothesis in_set_duplicate_elim : ∀ (S : Type) (r : brel S) (s : S) (X : finite_set S),
    in_set S r (uop_duplicate_elim S r X) s = in_set S r X s. 
*) 

  
End InSet. 











