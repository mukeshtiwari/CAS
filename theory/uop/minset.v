Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.combined. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.uop_properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.reduce. 
Require Import CAS.theory.brel.in_set.
Require Import CAS.theory.brel.subset.
Require Import CAS.theory.brel.set.



Lemma uop_minset_idempotent :  ∀ (S : Type) (eq : brel S) (lt : brel S),
   brel_reflexive S eq -> 
   brel_symmetric S eq -> 
   brel_transitive S eq -> 
   brel_congruence S eq lt -> 
   uop_idempotent (finite_set S) (brel_set S eq) (uop_minset S eq lt). 
Proof. intros S eq lt refS symS transS cong. unfold uop_idempotent.  intro s. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_uop_minset_elim in H; auto. destruct H as [A B]. 
          apply in_set_uop_minset_elim in B; auto. destruct B as [C D]. 
          apply in_set_uop_minset_intro; auto. 

          apply in_set_uop_minset_elim in H; auto. destruct H as [A B]. 
          apply in_set_uop_minset_intro; auto. 
          apply in_set_uop_minset_intro; auto. 
          apply is_minimal_in_idempotent; auto. 
Defined. 



Lemma uop_minset_congruence : 
   ∀ (S : Type) (eq : brel S) (lt : brel S),
      brel_reflexive S eq →
      brel_symmetric S eq →
      brel_transitive S eq →
      brel_congruence S eq lt →
         uop_congruence (finite_set S) (brel_minset S eq lt) (uop_minset S eq lt).  
Proof. intros S eq lt refS symS transS cong. 
       unfold brel_minset. 
       apply brel_reduce_uop_congruence. 
       apply idempotent_uop_uop_congruence. 
       apply brel_set_symmetric; auto. 
       apply brel_set_transitive; auto. 
       apply uop_minset_idempotent; auto.  
Defined. 





(*
   X = Y -> min(X) = min(Y) 
*) 
Lemma uop_minset_brel_set_congruence : 
   ∀ (S : Type) (eq : brel S) (lt : brel S),
     brel_reflexive S eq →
     brel_symmetric S eq →
     brel_transitive S eq →
     brel_congruence S eq lt →
         uop_congruence (finite_set S) (brel_set S eq) (uop_minset S eq lt).  
Proof. intros S eq lt refS symS transS cong. unfold uop_congruence . 
       intros s t H. 
       assert (C := is_minimal_in_right_congruence _ _ _ _ _ refS symS transS cong H). 
       apply brel_set_elim in H. destruct H as [H1 H2]. 
       apply brel_set_intro.  
       unfold uop_minset. unfold uop_filter_from_brel2. split. 
          apply brel_subset_uop_filter_intro; auto. 
          apply is_minimal_in_bProp_congruence; auto. 
          apply is_minimal_in_bProp_congruence; auto. 
          intros a K. rewrite (C a) in K. assumption. 

          apply brel_subset_uop_filter_intro; auto. 
          apply is_minimal_in_bProp_congruence; auto. 
          apply is_minimal_in_bProp_congruence; auto. 
          intros a K. rewrite (C a). assumption. 
Defined. 




Lemma uop_minset_preserves_left_positive : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
   brel_reflexive S eq →
   brel_symmetric S eq →
   brel_transitive S eq →
   brel_congruence S eq lt →
      uop_preserves_left_positive (finite_set S) (brel_minset S eq lt) (uop_minset S eq lt). 
Proof. intros S eq lt refS symS transS cong. unfold brel_minset. 
       apply brel_reduce_preserves_left_positive. 
          exact (brel_set S eq). (* why? *) 
          apply brel_set_transitive; auto. 
          apply uop_minset_brel_set_congruence; auto.
          apply uop_minset_idempotent; auto.  
Defined. 



Lemma uop_minset_preserves_left_negative : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
   brel_reflexive S eq →
   brel_symmetric S eq →
   brel_transitive S eq →
   brel_congruence S eq lt →
      uop_preserves_left_negative (finite_set S) (brel_minset S eq lt) (uop_minset S eq lt). 
Proof. intros S eq lt refS symS transS cong. unfold brel_minset. 
       apply brel_reduce_preserves_left_negative. 
          exact (brel_set S eq). (* why? *) 
          apply brel_set_symmetric; auto.  
          apply brel_set_transitive; auto. 
          apply uop_minset_brel_set_congruence; auto.
          apply uop_minset_idempotent; auto.  
Defined. 

