Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.subset.

Lemma brel_set_nil : 
   ∀ (S : Type) (eq : brel S) (X : finite_set S), 
    brel_set eq nil X = true -> X = nil. 
Proof. intros S eq. induction X; intro H. reflexivity. compute in H. discriminate. Defined. 


Lemma brel_set_intro : ∀ (S : Type) (eq : brel S) (X Y : finite_set S), 
     (brel_subset eq X Y = true) * (brel_subset eq Y X = true)  → brel_set eq X Y = true. 
Proof. intros S eq X Y [H1 H2]. unfold brel_set. unfold brel_and_sym. 
       apply andb_is_true_right; auto. 
Defined. 

Lemma brel_set_elim : ∀ (S : Type) (eq : brel S) (X Y : finite_set S), 
     brel_set eq X Y = true -> (brel_subset eq X Y = true) * (brel_subset eq Y X = true).
Proof. intros S eq X Y H. unfold brel_set in H. unfold brel_and_sym in H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]; auto. 
Defined. 

Lemma brel_set_intro_prop : ∀ (S : Type) (eq : brel S) (X Y : finite_set S), 
     brel_reflexive S eq →
     brel_symmetric S eq →
     brel_transitive S eq →
        (∀ a : S, in_set eq X a = true → in_set eq Y a = true) 
      * (∀ a : S, in_set eq Y a = true → in_set eq X a = true)  → 
             brel_set eq X Y = true. 
Proof. intros S eq X Y refS symS transS [H1 H2]. apply brel_set_intro. split. 
          apply brel_subset_intro in H1; auto. 
          apply brel_subset_intro in H2; auto. 
Defined. 

Lemma brel_set_elim_prop : ∀ (S : Type) (eq : brel S) (X Y : finite_set S), 
     brel_symmetric S eq →
     brel_transitive S eq →
     brel_set eq X Y = true -> 
        (∀ a : S, in_set eq X a = true → in_set eq Y a = true) 
      * (∀ a : S, in_set eq Y a = true → in_set eq X a = true).
Proof. intros S eq X Y symS transS H. unfold brel_set in H. unfold brel_and_sym in H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]. 
       assert (A1 := brel_subset_elim S eq symS transS _ _ H1). 
       assert (A2 := brel_subset_elim S eq symS transS _ _ H2); auto. 
Defined. 


(***     brel_set eqv properties   ****)

Lemma brel_and_sym_relexive : ∀ (S : Type) (r : brel S), 
              (brel_reflexive _ r) → brel_reflexive S (brel_and_sym r). 
Proof. intros S r. unfold brel_reflexive, brel_and_sym. intros refS s. 
       rewrite (refS s). simpl. reflexivity. 
Defined. 

Lemma brel_and_sym_transitive : ∀ (S : Type) (r : brel S), 
              (brel_transitive _ r) → brel_transitive S (brel_and_sym r). 
Proof. intros S r. unfold brel_transitive, brel_and_sym. intros transS s t u H1 H2. 
       apply andb_is_true_left in H1. destruct H1 as [H1_l H1_r].        
       apply andb_is_true_left in H2. destruct H2 as [H2_l H2_r].        
       rewrite (transS _ _ _ H1_l H2_l).
       rewrite (transS _ _ _ H2_r H1_r ). simpl. reflexivity. 
Defined. 

Lemma brel_and_sym_symmetric : ∀ (S : Type) (r : brel S), 
              brel_symmetric S (brel_and_sym r). 
Proof. intros S r. unfold brel_symmetric, brel_and_sym. intros s t H. 
       apply andb_is_true_left in H. destruct H as [H_l H_r].        
       rewrite H_l. rewrite H_r. simpl. reflexivity. 
Defined. 




Lemma brel_set_reflexive : ∀ (S : Type) (r : brel S), 
       brel_reflexive _ r →
       brel_symmetric S r →
       brel_transitive S r →
           brel_reflexive (finite_set S) (brel_set r). 
Proof. intros S r refS symS transS. unfold brel_set. 
       apply brel_and_sym_relexive. 
       apply brel_subset_reflexive; auto. 
Defined. 



Lemma brel_set_symmetric : ∀ (S : Type) (r : brel S), 
              (brel_symmetric _ r) → brel_symmetric (list S) (brel_set r). 
Proof. intros S r symS. unfold brel_set. apply brel_and_sym_symmetric. Defined. 

Lemma brel_set_transitive : ∀ (S : Type) (r : brel S), 
        (brel_reflexive _ r) → (brel_symmetric _ r) → (brel_transitive _ r) → 
         brel_transitive (finite_set S) (brel_set r). 
Proof. intros S r refS symS transS. 
       apply brel_and_sym_transitive. 
       apply brel_subset_transitive; auto. 
Defined. 

Lemma brel_set_congruence : 
  ∀ (S : Type) (eq : brel S), 
   brel_reflexive S eq →
   brel_symmetric S eq →
   brel_transitive S eq →
      brel_congruence (finite_set S) (brel_set eq) (brel_set eq). 
Proof. intros S eq refS symS transS. apply brel_congruence_self. 
       apply brel_set_symmetric; auto.  
       apply brel_set_transitive; auto.  
Defined. 



Lemma brel_set_not_trivial : ∀ (S : Type) (eq : brel S) (s : S), 
   brel_not_trivial (finite_set S) (brel_set eq) (λ (l : finite_set S), if brel_set eq nil l then (s :: nil) else nil). 
Proof. intros S eq s X. destruct X; compute; auto. Qed. 


(* 
Lemma brel_set_rep_correct : ∀ (S : Type)(eq : brel S)(rep : unary_op S), 
          brel_reflexive S eq →
          brel_symmetric S eq →
          brel_transitive S eq →
          brel_rep_correct S eq rep →
              brel_rep_correct (finite_set S) (brel_set S eq) (uop_set_rep S eq rep). 
Proof. intros S eq rep refS symS tranS P l. 
       apply brel_set_intro. split. 
          apply brel_subset_intro;auto. intros s H. 
          apply brel_subset_intro;auto. admit.  
Defined. 


Lemma brel_set_rep_idempotent : ∀ (S : Type)(eq : brel S)(rep : unary_op S), 
          brel_rep_idempotent S eq rep →
              brel_rep_idempotent (finite_set S) (brel_set S eq) (uop_set_rep S eq rep). 
Proof. intros S eq rep P l. induction l. 
       simpl. reflexivity. 
       simpl. apply andb_is_true_right. split. 
          apply P. 
          assumption. 
Defined. 
*) 