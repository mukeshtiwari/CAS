Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.uop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.brel.and_sym. 
Require Import CAS.theory.bop.then_unary. 
Require Import CAS.theory.bop.intersect. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.set.
Require Import CAS.theory.bop.union.
Require Import CAS.theory.bop.intersect.
Require Import CAS.theory.bops.add_ann_add_id. 
Require Import CAS.theory.bops.add_id_add_ann. 

(* 

Issue with (union, intersect): If the carrier set S is infinite, 
then the annihilator for intersect (id for union) is not a finite set. 
Even if S is a finite set, it can be enormous, with no good way 
of representing it.  Therefore, we define a constructon 
that forces the definition of a new constant representing 
the annihilator for intersect (id for union). 

The "bops_intersect_union_..._raw" results below capture the interaction 
of these binary operators before the id (annihilator) is added. 

*) 

(* ************************************* raw ************************************* *) 

Lemma bop_union_intersect_left_distributive_raw : ∀ (S : Type) (r : brel S),
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

Lemma bop_union_intersect_right_distributive_raw : ∀ (S : Type) (r : brel S),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_right_distributive (finite_set S) (brel_set S r) (bop_union S r) (bop_intersect S r). 
Proof. intros S r refS symS transS. 
       apply bop_left_distributive_implies_right; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bop_intersect_commutative_raw; auto. 
       apply bop_union_intersect_left_distributive_raw; auto. 
Defined. 


Lemma bops_union_intersect_left_left_absorptive_raw : ∀ (S : Type) (r : brel S),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_left_left_absorptive (finite_set S) (brel_set S r) (bop_union S r) (bop_intersect S r). 
Proof. intros S r refS symS transS s t. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_union_elim in H; auto. destruct H as [ H | H]. 
             assumption. 
             apply in_set_bop_intersect_elim in H; auto. destruct H as [L R].              
             assumption. 
Qed. 


Lemma bops_union_intersect_left_right_absorptive_raw : ∀ (S : Type) (r : brel S),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_left_right_absorptive (finite_set S) (brel_set S r) (bop_union S r) (bop_intersect S r) . 
Proof. intros S r refS symS transS. 
       apply bops_left_left_absorptive_implies_left_right. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence_raw; auto. 
       apply bop_intersect_commutative_raw; auto. 
       apply bops_union_intersect_left_left_absorptive_raw; auto. 
Qed. 


Lemma bops_union_intersect_right_left_absorptive_raw : ∀ (S : Type) (r : brel S),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_right_left_absorptive (finite_set S) (brel_set S r) (bop_union S r) (bop_intersect S r). 
Proof. intros S r refS symS transS. 
       apply bops_left_right_absorptive_implies_right_left. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bop_intersect_commutative_raw; auto. 
       apply bops_union_intersect_left_right_absorptive_raw; auto. 
Qed. 


Lemma bops_union_intersect_right_right_absorptive_raw : ∀ (S : Type) (r : brel S),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
       bops_right_right_absorptive (finite_set S) (brel_set S r) (bop_union S r) (bop_intersect S r). 
Proof. intros S r refS symS transS. 
       apply bops_right_left_absorptive_implies_right_right. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence_raw; auto. 
       apply bop_intersect_commutative_raw; auto. 
       apply bops_union_intersect_right_left_absorptive_raw; auto. 
Qed. 




(* ************************************* cooked ************************************* *) 

Lemma bops_union_intersect_left_distributive : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_left_distributive 
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_ann (finite_set S) (bop_union S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c refS symS transS. 
       apply bops_add_ann_add_id_left_distributive. 
       apply brel_set_reflexive; auto. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_intersect_left_left_absorptive_raw; auto. 
       apply bops_union_intersect_right_left_absorptive_raw; auto. 
       apply bop_union_intersect_left_distributive_raw; auto.        
Qed. 


Lemma bops_union_intersect_right_distributive : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_right_distributive 
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_ann (finite_set S) (bop_union S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c refS symS transS. 
       apply bops_add_ann_add_id_right_distributive. 
       apply brel_set_reflexive; auto. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_intersect_left_right_absorptive_raw; auto. 
       apply bops_union_intersect_right_right_absorptive_raw; auto. 
       apply bop_union_intersect_right_distributive_raw; auto.        
Qed. 


Lemma bops_union_intersect_left_left_absorptive : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_left_left_absorptive 
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_ann (finite_set S) (bop_union S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c refS symS transS. 
       apply bops_add_ann_add_id_left_left_absorptive. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_intersect_left_left_absorptive_raw; auto. 
Qed. 


Lemma bops_union_intersect_left_right_absorptive : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_left_right_absorptive 
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_ann (finite_set S) (bop_union S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c refS symS transS. 
       apply bops_add_ann_add_id_left_right_absorptive. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_intersect_left_right_absorptive_raw; auto. 
Qed. 

Lemma bops_union_intersect_right_left_absorptive : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_right_left_absorptive 
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_ann (finite_set S) (bop_union S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c refS symS transS. 
       apply bops_add_ann_add_id_right_left_absorptive. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_intersect_right_left_absorptive_raw; auto. 
Qed. 


Lemma bops_union_intersect_right_right_absorptive : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_right_right_absorptive 
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_ann (finite_set S) (bop_union S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c).
Proof. intros S r c refS symS transS. 
       apply bops_add_ann_add_id_right_right_absorptive. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_intersect_right_right_absorptive_raw; auto. 
Qed. 


Lemma bops_union_intersect_id_equals_ann : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bops_id_equals_ann 
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_ann (finite_set S) (bop_union S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c refS symS transS. 
       apply bops_add_ann_add_id_id_equals_ann. 
       apply brel_set_reflexive; auto. 
       unfold bops_id_equals_ann. 
       exists (bop_union_exists_id_raw S r refS symS transS). 
       exists (bop_intersect_exists_ann_raw S r refS symS transS). 
       compute. reflexivity. 
Qed. 

Lemma bops_union_intersect_ann_equals_id : ∀ (S : Type) (r : brel S) (c : cas_constant),
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







