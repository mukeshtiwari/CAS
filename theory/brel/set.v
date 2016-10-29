Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.and_sym. 
Require Import CAS.theory.brel.in_set.
Require Import CAS.theory.brel.subset.

Lemma brel_set_nil : 
   ∀ (S : Type) (eq : brel S) (X : finite_set S), 
    brel_set S eq nil X = true -> X = nil. 
Proof. intros S eq. induction X; intro H. reflexivity. compute in H. discriminate. Defined. 


Lemma brel_set_intro : ∀ (S : Type) (eq : brel S) (X Y : finite_set S), 
     (brel_subset S eq X Y = true) * (brel_subset S eq Y X = true)  → brel_set S eq X Y = true. 
Proof. intros S eq X Y [H1 H2]. unfold brel_set. unfold brel_and_sym. 
       apply andb_is_true_right; auto. 
Defined. 

Lemma brel_set_elim : ∀ (S : Type) (eq : brel S) (X Y : finite_set S), 
     brel_set S eq X Y = true -> (brel_subset S eq X Y = true) * (brel_subset S eq Y X = true).
Proof. intros S eq X Y H. unfold brel_set in H. unfold brel_and_sym in H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]; auto. 
Defined. 

Lemma brel_set_intro_prop : ∀ (S : Type) (eq : brel S) (X Y : finite_set S), 
     brel_reflexive S eq →
     brel_symmetric S eq →
     brel_transitive S eq →
        (∀ a : S, in_set S eq X a = true → in_set S eq Y a = true) 
      * (∀ a : S, in_set S eq Y a = true → in_set S eq X a = true)  → 
             brel_set S eq X Y = true. 
Proof. intros S eq X Y refS symS transS [H1 H2]. apply brel_set_intro. split. 
          apply brel_subset_intro in H1; auto. 
          apply brel_subset_intro in H2; auto. 
Defined. 

Lemma brel_set_elim_prop : ∀ (S : Type) (eq : brel S) (X Y : finite_set S), 
     brel_symmetric S eq →
     brel_transitive S eq →
     brel_set S eq X Y = true -> 
        (∀ a : S, in_set S eq X a = true → in_set S eq Y a = true) 
      * (∀ a : S, in_set S eq Y a = true → in_set S eq X a = true).
Proof. intros S eq X Y symS transS H. unfold brel_set in H. unfold brel_and_sym in H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]. 
       assert (A1 := brel_subset_elim S eq symS transS _ _ H1). 
       assert (A2 := brel_subset_elim S eq symS transS _ _ H2); auto. 
Defined. 


(***     brel_set eqv properties   ****) 

Lemma brel_set_reflexive : ∀ (S : Type) (r : brel S), 
       brel_reflexive _ r →
       brel_symmetric S r →
       brel_transitive S r →
           brel_reflexive (finite_set S) (brel_set S r). 
Proof. intros S r refS symS transS. unfold brel_set. 
       apply brel_and_sym_relexive. 
       apply brel_subset_reflexive; auto. 
Defined. 



Lemma brel_set_symmetric : ∀ (S : Type) (r : brel S), 
              (brel_symmetric _ r) → brel_symmetric (list S) (brel_set S r). 
Proof. intros S r symS. unfold brel_set. apply brel_and_sym_symmetric. Defined. 

Lemma brel_set_transitive : ∀ (S : Type) (r : brel S), 
        (brel_reflexive _ r) → (brel_symmetric _ r) → (brel_transitive _ r) → 
         brel_transitive (finite_set S) (brel_set S r). 
Proof. intros S r refS symS transS. 
       apply brel_and_sym_transitive. 
       apply brel_subset_transitive; auto. 
Defined. 

Lemma brel_set_congruence : 
  ∀ (S : Type) (eq : brel S), 
   brel_reflexive S eq →
   brel_symmetric S eq →
   brel_transitive S eq →
      brel_congruence (finite_set S) (brel_set S eq) (brel_set S eq). 
Proof. intros S eq refS symS transS. apply brel_congruence_self. 
       apply brel_set_symmetric; auto.  
       apply brel_set_transitive; auto.  
Defined. 


Lemma brel_set_witness : ∀ (S : Type) (r : brel S), brel_witness (finite_set S) (brel_set S r). 
Proof. intros S r. exists nil; auto. Defined.

Lemma brel_set_negate : ∀ (S : Type) (r : brel S), 
              (brel_symmetric S r) → 
              (brel_witness S r) → brel_negate (finite_set S) (brel_set S r). 
Proof. unfold brel_negate. intros S r symS [s P].  
       exists (λ (l : finite_set S), if brel_set S r nil l then (s :: nil) else nil). 
       intro l; simpl. 
       case_eq(brel_set S r nil l); intro J.
          rewrite (brel_set_nil S r l J). compute. auto. 
          rewrite J. 
          assert (brel_set_sym := brel_set_symmetric S r symS). 
          assert (F := brel_symmetric_implies_dual _ _ brel_set_sym _ _ J). 
          rewrite F. auto. 
Defined. 

Definition brel_set_nontrivial : ∀ (S : Type) (r : brel S), 
       (brel_symmetric _ r) → 
       (brel_nontrivial S r) → brel_nontrivial (finite_set S) (brel_set S r)
:= λ S r symS nt, 
   {| 
      brel_nontrivial_witness := brel_set_witness S r
    ; brel_nontrivial_negate  := brel_set_negate S r symS (brel_nontrivial_witness _ _ nt)
   |}. 


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