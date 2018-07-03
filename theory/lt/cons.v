Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.trans. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.lt_properties. 
Require Import CAS.theory.brel.eq_list. 
Require Import CAS.theory.facts. 
Section Cons. 

Variable S : Type. 
Variable r : brel S.

Variable wS : S.
Variable f  : S -> S.
Variable Pf : brel_not_trivial S r f. 

Variable refS : brel_reflexive S r. 

Lemma lt_cons_congruence : lt_congruence S (list S) r (brel_list r) (@lt_cons S).
Proof. unfold lt_congruence, lt_cons. intros h1 h2. 
       induction s1; induction s2; unfold brel_list; intros H Q. 
       rewrite H. simpl. reflexivity. 
       discriminate. discriminate. 
       fold @brel_list. fold @brel_list in Q. apply andb_is_true_left in Q. destruct Q as [L R]. 
       rewrite H, L, R. simpl. reflexivity. 
Qed. 


Lemma lt_cons_not_is_right : lt_not_is_right S (list S) (brel_list r) (@lt_cons S).
Proof. unfold lt_cons, lt_not_is_right. exists (wS, nil). compute. reflexivity. Defined. 

Lemma lt_cons_not_is_id : ∀ s : S,  lt_not_is_id S (list S) (brel_list r) (@lt_cons S) s.
Proof. intro s. unfold lt_not_is_id. exists nil. compute. reflexivity. Defined. 

Lemma lt_cons_not_exists_id : lt_not_exists_id S (list S) (brel_list r) (@lt_cons S).
Proof. intro l. apply lt_cons_not_is_id. Qed. 


Lemma brel_list_cons : ∀ (a : S) (l1 l2 : list S), brel_list r (a :: l1) (a :: l2) = brel_list  r l1 l2. 
Proof. intros a l1 l2. unfold brel_list at 1. fold @brel_list. 
       rewrite (refS a). simpl. reflexivity. 
Qed. 

Lemma  lt_cons_left_cancellative : lt_left_cancellative S (list S) (brel_list r) (@lt_cons S).
Proof. unfold lt_left_cancellative, lt_cons. intros s l1 l2 H.
       assert (F := brel_list_cons s l1 l2). 
       rewrite H in F. rewrite <- F. reflexivity.        
Qed.        

Lemma lt_cons_right_cancellative : 
         lt_right_cancellative S (list S) r (brel_list r) (@lt_cons S).
Proof. unfold lt_right_cancellative, lt_cons. intros s1 s2 l. 
       unfold brel_list. fold @brel_list.
       rewrite brel_list_reflexive; auto. simpl. intro H. 
       apply andb_is_true_left in H. destruct H as [H _]. rewrite H. reflexivity. 
Qed. 

Lemma  lt_cons_not_left_constant : lt_not_left_constant S (list S) (brel_list r) (@lt_cons S).
Proof. unfold lt_not_left_constant, lt_cons. exists (wS, (nil, wS :: nil)); simpl. rewrite (refS wS). simpl. reflexivity. Defined. 

Lemma  lt_cons_not_right_constant : lt_not_right_constant S (list S) (brel_list r) (@lt_cons S).
Proof. exists (wS, (f wS, nil)); simpl.
       destruct (Pf wS) as [F _].  rewrite F. simpl. reflexivity.
Defined. 

Lemma  lt_cons_anti_right : lt_anti_right S (list S) (brel_list r) (@lt_cons S).
Proof. unfold lt_anti_right, lt_cons. intros s l.
       induction l.        
          unfold brel_list; fold @brel_list. reflexivity. 
          admit. 
Admitted. 

End Cons.