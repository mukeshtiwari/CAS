Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.uop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.brel_and_sym. 
Require Import CAS.theory.bop_then_unary. 
Require Import CAS.theory.bop_intersect. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel2_in_set.
Require Import CAS.theory.brel_subset.
Require Import CAS.theory.brel_set.
Require Import CAS.theory.uop_duplicate_elim. 
Require Import CAS.theory.bop_union.
Require Import CAS.theory.bop_intersect.



Lemma bop_union_intersect_left_distributive : ∀ (S : Type) (r : brel S),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_left_distributive (finite_set S) (brel_set S r) (bop_union S r) (bop_intersect S r). 
Proof. intros S r refS symS transS s t u. 
       apply brel_set_intro_prop; auto. split; intros a H.        
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_intersect_elim in H; auto. destruct H as [ L R ]. 
          apply in_set_bop_union_elim in R; auto. destruct R as [R | R].
             left. apply in_set_bop_intersect_intro; auto. 
             right. apply in_set_bop_intersect_intro; auto. 
       apply in_set_bop_intersect_intro; auto. 
       apply in_set_bop_union_elim in H; auto. 
       destruct H as [H | H]; split; apply in_set_bop_intersect_elim in H; 
       destruct H as [ L R ]; auto.  
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_union_intro; auto. 
Qed. 

Lemma bop_union_intersect_right_distributive : ∀ (S : Type) (r : brel S),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_right_distributive (finite_set S) (brel_set S r) (bop_union S r) (bop_intersect S r). 
Proof. intros S r refS symS transS. 
       apply bop_left_distributive_implies_right; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence; auto. 
       apply bop_union_commutative; auto. 
       apply bop_intersect_commutative; auto. 
       apply bop_union_intersect_left_distributive; auto. 
Defined. 


Lemma bops_union_intersect_left_absorptive : ∀ (S : Type) (r : brel S),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_left_absorption (finite_set S) (brel_set S r) (bop_union S r) (bop_intersect S r). 
Proof. intros S r refS symS transS s t. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_union_elim in H; auto. destruct H as [ H | H]. 
             assumption. 
             apply in_set_bop_intersect_elim in H; auto. destruct H as [L R].              
             assumption. 
Qed. 


Lemma bops_union_intersect_right_absorptive : ∀ (S : Type) (r : brel S),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_right_absorption (finite_set S) (brel_set S r) (bop_union S r) (bop_intersect S r). 
Proof. intros S r refS symS transS s t. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_union_elim in H; auto. destruct H as [ H | H]. 
             assumption. 
             apply in_set_bop_intersect_elim in H; auto. destruct H as [L R].              
             assumption. 
Qed. 


Lemma intersect_union_id_equals_ann : ∀ (S : Type) (r : brel S), 
     brel_reflexive S r -> 
     brel_symmetric S r -> 
     brel_transitive S r -> 
      bops_id_equals_ann (finite_set S) (brel_set S r) (bop_union S r) (bop_intersect S r).
Proof. intros S r refS symS transS. unfold bops_id_equals_ann. 
       exists (bop_union_exists_id S r refS symS transS). 
       exists (bop_intersect_exists_ann S r refS symS transS). 
       compute. reflexivity. 
Defined. 







