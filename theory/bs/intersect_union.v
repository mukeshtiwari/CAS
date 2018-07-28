Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.combined. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bs_properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.set.
Require Import CAS.theory.bop.union.
Require Import CAS.theory.bop.intersect.
Require Import CAS.theory.bs.add_ann_add_id. 
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

Section IntersectUnion.
  Variable S: Type.
  Variable r : brel S.
  Variable wS  : S. 
  Variable f : S -> S.
  Variable ntS : brel_not_trivial S r f. 
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.

(* ************************************* raw ************************************* *) 

Lemma bop_intersect_union_left_distributive_raw : 
        bop_left_distributive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. intros s t u. 
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

Lemma bop_intersect_union_right_distributive_raw : 
        bop_right_distributive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. apply bop_left_distributive_implies_right; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence_raw; auto. 
       apply bop_intersect_commutative_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bop_intersect_union_left_distributive_raw; auto. 
Qed. 

Lemma bops_intersect_union_left_left_absorptive_raw : 
        bops_left_left_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. intros s t. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_intersect_intro; auto. split; auto. 
             apply in_set_bop_union_intro; auto. 
          apply in_set_bop_intersect_elim in H; auto. destruct H as [ L R ]; auto. 
Qed. 


Lemma bops_intersect_union_left_right_absorptive_raw : 
        bops_left_right_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. apply bops_left_left_absorptive_implies_left_right. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bops_intersect_union_left_left_absorptive_raw; auto. 
Qed. 


Lemma bops_intersect_union_right_left_absorptive_raw : 
        bops_right_left_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. apply bops_left_right_absorptive_implies_right_left. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence_raw; auto. 
       apply bop_intersect_commutative_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bops_intersect_union_left_right_absorptive_raw; auto. 
Qed. 

Lemma bops_intersect_union_right_right_absorptive_raw : 
        bops_right_right_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. apply bops_right_left_absorptive_implies_right_right. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bops_intersect_union_right_left_absorptive_raw; auto. 
Qed. 

(* ************************************* cooked ************************************* *) 

Variable c : cas_constant. 
Lemma bops_intersect_union_left_distributive : 
        bop_left_distributive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_left_distributive. 
       apply brel_set_reflexive; auto. 
       apply bop_intersect_union_left_distributive_raw; auto.        
Qed. 


Lemma bops_intersect_union_right_distributive : 
        bop_right_distributive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_right_distributive. 
       apply brel_set_reflexive; auto. 
       apply bop_intersect_union_right_distributive_raw; auto.        
Qed. 


Lemma bops_intersect_union_left_left_absorptive : 
        bops_left_left_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_left_left_absorptive. 
       apply brel_set_reflexive; auto. 
       apply bops_intersect_union_left_left_absorptive_raw; auto. 
Qed. 


Lemma bops_intersect_union_left_right_absorptive : 
        bops_left_right_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_left_right_absorptive. 
       apply brel_set_reflexive; auto. 
       apply bops_intersect_union_left_right_absorptive_raw; auto. 
Qed. 

Lemma bops_intersect_union_right_left_absorptive : 
        bops_right_left_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_right_left_absorptive. 
       apply brel_set_reflexive; auto. 
       apply bops_intersect_union_right_left_absorptive_raw; auto. 
Qed. 


Lemma bops_intersect_union_right_right_absorptive : 
        bops_right_right_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_right_right_absorptive. 
       apply brel_set_reflexive; auto. 
       apply bops_intersect_union_right_right_absorptive_raw; auto. 
Qed. 


Lemma bops_intersect_union_id_equals_ann : 
        bops_id_equals_ann 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_id_equals_ann. 
       apply brel_set_reflexive; auto. 
Qed. 


Lemma bops_intersect_union_ann_equals_id : 
        bops_id_equals_ann 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c). 
Proof. apply bops_add_id_add_ann_ann_equals_id. 
       apply brel_set_reflexive; auto. 
       exists nil; split. 
       apply bop_union_nil_is_id; auto.
       apply bop_intersect_nil_is_ann; auto.        
Qed.

End IntersectUnion.



