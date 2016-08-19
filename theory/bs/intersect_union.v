Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bs_properties. 



Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.set.
Require Import CAS.theory.bop.intersect. 
Require Import CAS.theory.bop.union.
Require Import CAS.theory.bs.add_id_add_ann. 

(* 

Issue with (intersect, union): If the carrier set S is infinite, 
then the id for intersect (annihilator for union) is not a finite set. 
Even if S is a finite set, it can be enormous, with no good way 
of representing it.  Therefore, we define a constructon 
that forces the definition of a new constant representing 
the id for intersect (annihilator for union). 

The "bops_intersect_union_..._raw" results below capture the interaction 
of these binary operators before the id (annihilator) is added. 

*) 

(* ************************************* raw ************************************* *) 

Lemma bop_intersect_union_left_distributive_raw : ∀ (S : Type) (r : brel S),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_left_distributive (finite_set S) (brel_set S r) (bop_intersect S r) (bop_union S r). 
Proof. intros S r refS symS transS s t u. 
       apply brel_set_intro_prop; auto. split; intros a H.        
          apply in_set_bop_intersect_intro; auto. split; apply in_set_bop_union_intro; auto. 
             apply in_set_bop_union_elim in H; auto. destruct H as [H | H ]. 
                left. assumption. 
                apply in_set_bop_intersect_elim in H; auto. destruct H as [ L R ]. 
                right. assumption. 
             apply in_set_bop_union_elim in H; auto. destruct H as [H | H ]. 
                left. assumption. 
                apply in_set_bop_intersect_elim in H; auto. destruct H as [ L R ]. 
                right. assumption. 
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_intersect_elim in H; auto. destruct H as [ L R ]. 
          apply in_set_bop_union_elim in L; apply in_set_bop_union_elim in R; auto. 
          destruct L as [L |L]; destruct R as [R | R]. 
             left. assumption. 
             left. assumption. 
             left. assumption. 
             right. apply in_set_bop_intersect_intro; auto. 
Qed. 

Lemma bop_intersect_union_right_distributive_raw : ∀ (S : Type) (r : brel S),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_right_distributive (finite_set S) (brel_set S r) (bop_intersect S r) (bop_union S r). 
Proof. intros S r refS symS transS. 
       apply bop_left_distributive_implies_right; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence_raw; auto. 
       apply bop_intersect_commutative_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bop_intersect_union_left_distributive_raw; auto. 
Qed. 

Lemma bops_intersect_union_left_left_absorptive_raw : ∀ (S : Type) (r : brel S),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_left_left_absorptive (finite_set S) (brel_set S r) (bop_intersect S r) (bop_union S r). 
Proof. intros S r refS symS transS s t. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_intersect_intro; auto. split. 
             assumption. 
             apply in_set_bop_union_intro; auto. 
          apply in_set_bop_intersect_elim in H; auto. destruct H as [ L R ]. 
          assumption. 
Qed. 


Lemma bops_intersect_union_left_right_absorptive_raw : ∀ (S : Type) (r : brel S),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_left_right_absorptive (finite_set S) (brel_set S r) (bop_intersect S r) (bop_union S r). 
Proof. intros S r refS symS transS. 
       apply bops_left_left_absorptive_implies_left_right. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bops_intersect_union_left_left_absorptive_raw; auto. 
Qed. 


Lemma bops_intersect_union_right_left_absorptive_raw : ∀ (S : Type) (r : brel S),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_right_left_absorptive (finite_set S) (brel_set S r) (bop_intersect S r) (bop_union S r). 
Proof. intros S r refS symS transS. 
       apply bops_left_right_absorptive_implies_right_left. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence_raw; auto. 
       apply bop_intersect_commutative_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bops_intersect_union_left_right_absorptive_raw; auto. 
Qed. 


Lemma bops_intersect_union_right_right_absorptive_raw : ∀ (S : Type) (r : brel S),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_right_right_absorptive (finite_set S) (brel_set S r) (bop_intersect S r) (bop_union S r). 
Proof. intros S r refS symS transS. 
       apply bops_right_left_absorptive_implies_right_right. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bops_intersect_union_right_left_absorptive_raw; auto. 
Qed. 




(* ************************************* cooked ************************************* *) 

Lemma bops_intersect_union_left_distributive : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_left_distributive 
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c)
            (bop_add_ann (finite_set S) (bop_union S r) c). 
Proof. intros S r c refS symS transS. 
       apply bops_add_id_add_ann_left_distributive. 
       apply brel_set_reflexive; auto. 
       apply bop_intersect_union_left_distributive_raw; auto.        
Qed. 


Lemma bops_intersect_union_right_distributive : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_right_distributive 
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c)
            (bop_add_ann (finite_set S) (bop_union S r) c). 
Proof. intros S r c refS symS transS. 
       apply bops_add_id_add_ann_right_distributive. 
       apply brel_set_reflexive; auto. 
       apply bop_intersect_union_right_distributive_raw; auto.        
Qed. 


Lemma bops_intersect_union_left_left_absorptive : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_left_left_absorptive 
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c)
            (bop_add_ann (finite_set S) (bop_union S r) c). 
Proof. intros S r c refS symS transS. 
       apply bops_add_id_add_ann_left_left_absorptive. 
       apply brel_set_reflexive; auto. 
       apply bops_intersect_union_left_left_absorptive_raw; auto. 
Qed. 


Lemma bops_intersect_union_left_right_absorptive : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_left_right_absorptive 
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c)
            (bop_add_ann (finite_set S) (bop_union S r) c). 
Proof. intros S r c refS symS transS. 
       apply bops_add_id_add_ann_left_right_absorptive. 
       apply brel_set_reflexive; auto. 
       apply bops_intersect_union_left_right_absorptive_raw; auto. 
Qed. 

Lemma bops_intersect_union_right_left_absorptive : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_right_left_absorptive 
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c)
            (bop_add_ann (finite_set S) (bop_union S r) c). 
Proof. intros S r c refS symS transS. 
       apply bops_add_id_add_ann_right_left_absorptive. 
       apply brel_set_reflexive; auto. 
       apply bops_intersect_union_right_left_absorptive_raw; auto. 
Qed. 


Lemma bops_intersect_union_right_right_absorptive : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_right_right_absorptive 
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c)
            (bop_add_ann (finite_set S) (bop_union S r) c). 
Proof. intros S r c refS symS transS. 
       apply bops_add_id_add_ann_right_right_absorptive. 
       apply brel_set_reflexive; auto. 
       apply bops_intersect_union_right_right_absorptive_raw; auto. 
Qed. 


Lemma bops_intersect_union_id_equals_ann : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_id_equals_ann 
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c)
            (bop_add_ann (finite_set S) (bop_union S r) c). 
Proof. intros S r c refS symS transS. 
       apply bops_add_id_add_ann_id_equals_ann. 
       apply brel_set_reflexive; auto. 
Qed. 


Lemma bops_intersect_union_ann_equals_id : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_id_equals_ann 
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_ann (finite_set S) (bop_union S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c refS symS transS. 
       apply bops_add_id_add_ann_ann_equals_id. 
       apply brel_set_reflexive; auto. 
       unfold bops_id_equals_ann. 
       exists (bop_union_exists_id_raw S r refS symS transS). 
       exists (bop_intersect_exists_ann_raw S r refS symS transS). 
       compute. reflexivity. 
Qed. 



