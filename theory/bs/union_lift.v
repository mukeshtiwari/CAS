Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.combined. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.bs_properties. 
Require Import CAS.theory.facts.
Require Import CAS.theory.brel.in_set.
Require Import CAS.theory.brel.subset. 
Require Import CAS.theory.brel.set.
Require Import CAS.theory.bop.union.
Require Import CAS.theory.bop.lift.
Require Import CAS.theory.bs.add_ann_add_id. 
Require Import CAS.theory.bs.add_id_add_ann. 



Section UnionIntersect.
  Variable S: Type.
  Variable r : brel S.
  Variable wS  : S. 
  Variable f : S -> S.
  Variable ntS : brel_not_trivial S r f. 
  Variable bS : binary_op S.
  
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.
  
  Variable bcong : bop_congruence S r bS. 
  Variable assS : bop_associative S r bS. 


Lemma bop_union_lift_left_distributive_raw : 
        bop_left_distributive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros X Y Z. 
       apply brel_set_intro_prop; auto.
       split; intros a H.        
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_lift_elim in H;
          auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
          apply in_set_bop_union_elim in P2; auto.
          destruct P2 as [R | R].
             left. apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong X Y a x y); auto. 
             right. apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong X Z a x y); auto. 
       
       apply in_set_bop_union_elim in H; auto. destruct H as [H | H].
       apply in_set_bop_lift_elim in H; auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
       apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong X (bop_union r Y Z) a x y); auto.
       apply in_set_bop_union_intro; auto.
       apply in_set_bop_lift_elim in H; auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
       apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong X (bop_union r Y Z) a x y); auto.
       apply in_set_bop_union_intro; auto. 
Qed. 


Lemma bop_union_lift_right_distributive_raw : 
        bop_right_distributive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros X Y Z. 
       apply brel_set_intro_prop; auto.
       split; intros a H.        
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_lift_elim in H;
          auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
          apply in_set_bop_union_elim in P1; auto.
          destruct P1 as [R | R].
             left. apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong Y X a x y); auto. 
             right. apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong Z X a x y); auto. 
       
       apply in_set_bop_union_elim in H; auto. destruct H as [H | H].
       apply in_set_bop_lift_elim in H; auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
       apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong (bop_union r Y Z) X a x y); auto.
       apply in_set_bop_union_intro; auto.
       apply in_set_bop_lift_elim in H; auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
       apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong (bop_union r Y Z) X a x y); auto.
       apply in_set_bop_union_intro; auto. 
Qed. 



Lemma bops_union_lift_left_left_absorptive_raw : 
        bop_is_left S r bS -> bops_left_left_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros IL X Y. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_union_elim in H; auto. destruct H as [ H | H]; auto. 
             apply in_set_bop_lift_elim in H; auto. destruct H as [x [y [[H1 H2] H3]]].
             assert (H4 := IL x y).
             assert (H5 := tranS _ _ _ H3 H4).
             apply symS in H5. assert (H6 := in_set_right_congruence _ _ symS tranS _ _ _ H5 H1). exact H6. 
Qed. 

Lemma bops_union_lift_not_left_left_absorptive_raw : 
        bop_not_is_left S r bS -> bops_not_left_left_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros [[s t] P]. unfold bops_not_left_left_absorptive. 
       exists (s :: nil, t :: nil).
       case_eq(brel_set r (s :: nil) (bop_union r (s :: nil) (bop_lift r bS (s :: nil) (t :: nil)))); intro J1; auto.
          apply brel_set_elim in J1. destruct J1 as [L R].
          assert (K1 := brel_subset_elim _ _ symS tranS _ _ R (bS s t)).
          assert (K2 : in_set r (bop_union r (s :: nil) (bop_lift r bS (s :: nil) (t :: nil))) (bS s t) = true).
             apply in_set_bop_union_intro; auto.
             right. apply in_set_bop_lift_intro; auto.
             apply in_set_singleton_intro; auto.
             apply in_set_singleton_intro; auto.              
          assert (K3 := K1 K2).
          apply in_set_singleton_elim in K3; auto.
          apply symS in K3. rewrite K3 in P. discriminate P. 
Qed. 

Lemma bops_union_lift_left_right_absorptive_raw : 
        bop_is_right S r bS -> bops_left_right_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros IR X Y. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_union_elim in H; auto. destruct H as [ H | H]; auto. 
             apply in_set_bop_lift_elim in H; auto. destruct H as [x [y [[H1 H2] H3]]].
             assert (H4 := IR x y).
             assert (H5 := tranS _ _ _ H3 H4).
             apply symS in H5. assert (H6 := in_set_right_congruence _ _ symS tranS _ _ _ H5 H2). exact H6. 
Qed. 

Lemma bops_union_lift_not_left_right_absorptive_raw : 
        bop_not_is_right S r bS -> bops_not_left_right_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros [[s t] P]. 
       exists (t :: nil, s :: nil).
       case_eq(brel_set r (t :: nil) (bop_union r (t :: nil) (bop_lift r bS (s :: nil) (t :: nil)))); intro J1; auto.
          apply brel_set_elim in J1. destruct J1 as [L R].
          assert (K1 := brel_subset_elim _ _ symS tranS _ _ R (bS s t)).
          assert (K2 : in_set r (bop_union r (t :: nil) (bop_lift r bS (s :: nil) (t :: nil))) (bS s t) = true).
             apply in_set_bop_union_intro; auto.
             right. apply in_set_bop_lift_intro; auto.
             apply in_set_singleton_intro; auto.
             apply in_set_singleton_intro; auto.              
          assert (K3 := K1 K2).
          apply in_set_singleton_elim in K3; auto.
          apply symS in K3. rewrite K3 in P. discriminate P. 
Qed. 


Lemma bops_union_lift_right_left_absorptive_raw : 
        bop_is_left S r bS -> bops_right_left_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros IL. 
       apply bops_left_left_absorptive_implies_right_left.
       apply brel_set_transitive; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bops_union_lift_left_left_absorptive_raw; auto. 
Qed. 


Lemma bops_union_lift_not_right_left_absorptive_raw : 
        bop_not_is_left S r bS -> bops_not_right_left_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros NIL. 
       apply bops_not_left_left_absorptive_implies_not_right_left.
       apply brel_set_transitive; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bops_union_lift_not_left_left_absorptive_raw; auto. 
Qed. 


Lemma bops_union_lift_right_right_absorptive_raw : 
        bop_is_right S r bS -> bops_right_right_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros IR. 
       apply bops_left_right_absorptive_implies_right_right.
       apply brel_set_transitive; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bops_union_lift_left_right_absorptive_raw; auto. 
Qed. 

Lemma bops_union_lift_not_right_right_absorptive_raw : 
        bop_not_is_right S r bS -> bops_not_right_right_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros NIR. 
       apply bops_not_left_right_absorptive_implies_not_right_right.
       apply brel_set_transitive; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bops_union_lift_not_left_right_absorptive_raw; auto. 
Qed. 



(* ************************************* cooked ************************************* *) 

Variable c : cas_constant.

Lemma bops_union_lift_left_distributive :
        bop_is_left S r bS -> (*********** NB ************)
        bop_left_distributive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intro IL.
       apply bops_add_ann_add_id_left_distributive. 
       apply brel_set_reflexive; auto. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_lift_left_left_absorptive_raw; auto. 
       apply bops_union_lift_right_left_absorptive_raw; auto. 
       apply bop_union_lift_left_distributive_raw; auto.        
Qed. 


Lemma bops_union_lift_not_left_distributive :
        bop_not_is_left S r bS -> (*********** NB ************)
        bop_not_left_distributive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intro NIL.
       apply bops_add_ann_add_id_not_left_distributive; auto. 
       apply brel_set_symmetric; auto.
       left. left. right. 
       apply bops_union_lift_not_left_left_absorptive_raw; auto. 
Qed. 


Lemma bops_union_lift_right_distributive :
        bop_is_right S r bS -> (*********** NB ************)
        bop_right_distributive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intro IR.
       apply bops_add_ann_add_id_right_distributive. 
       apply brel_set_reflexive; auto. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_lift_left_right_absorptive_raw; auto. 
       apply bops_union_lift_right_right_absorptive_raw; auto. 
       apply bop_union_lift_right_distributive_raw; auto.        
Qed.

Lemma bops_union_lift_not_right_distributive :
        bop_not_is_right S r bS -> (*********** NB ************)
        bop_not_right_distributive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intro NIR.
       apply bops_add_ann_add_id_not_right_distributive; auto. 
       apply brel_set_symmetric; auto.
       left. left. right. 
       apply bops_union_lift_not_left_right_absorptive_raw; auto. 
Qed. 


Lemma bops_union_lift_left_left_absorptive :
        bop_is_left S r bS -> (*********** NB ************)
        bops_left_left_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intro IL.
       apply bops_add_ann_add_id_left_left_absorptive. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_lift_left_left_absorptive_raw; auto. 
Qed. 

Lemma bops_union_lift_not_left_left_absorptive :
        bop_not_is_left S r bS -> (*********** NB ************)
        bops_not_left_left_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intro NIL.
       apply bops_add_ann_add_id_not_left_left_absorptive; auto. 
       apply brel_set_symmetric; auto. 
       right. apply bops_union_lift_not_left_left_absorptive_raw; auto. 
Qed. 



Lemma bops_union_lift_left_right_absorptive :
    bop_is_right S r bS -> 
        bops_left_right_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intro IR.
       apply bops_add_ann_add_id_left_right_absorptive. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_lift_left_right_absorptive_raw; auto. 
Qed.

Lemma bops_union_lift_not_left_right_absorptive :
        bop_not_is_right S r bS -> 
        bops_not_left_right_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intro NIR.
       apply bops_add_ann_add_id_not_left_right_absorptive; auto. 
       apply brel_set_symmetric; auto. 
       right. apply bops_union_lift_not_left_right_absorptive_raw; auto. 
Qed. 


Lemma bops_union_lift_right_left_absorptive :
  bop_is_left S r bS ->   
        bops_right_left_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intro IL.
       apply bops_add_ann_add_id_right_left_absorptive. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_lift_right_left_absorptive_raw; auto. 
Qed. 

Lemma bops_union_lift_not_right_left_absorptive :
        bop_not_is_left S r bS -> (*********** NB ************)
        bops_not_right_left_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intro NIL.
       apply bops_add_ann_add_id_not_right_left_absorptive; auto. 
       apply brel_set_symmetric; auto. 
       right. apply bops_union_lift_not_right_left_absorptive_raw; auto. 
Qed. 

Lemma bops_union_lift_right_right_absorptive :
    bop_is_right S r bS -> 
        bops_right_right_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c).
Proof. intro NIR.
       apply bops_add_ann_add_id_right_right_absorptive. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_lift_right_right_absorptive_raw; auto. 
Qed. 

Lemma bops_union_lift_not_right_right_absorptive :
        bop_not_is_right S r bS -> 
        bops_not_right_right_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intro NIR.
       apply bops_add_ann_add_id_not_right_right_absorptive; auto. 
       apply brel_set_symmetric; auto. 
       right. apply bops_union_lift_not_right_right_absorptive_raw; auto. 
Qed. 

Lemma bops_union_lift_ann_equals_id : 
        bops_id_equals_ann 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_id_equals_ann. 
       apply brel_set_reflexive; auto. 
Qed. 


Lemma bops_union_lift_id_equals_ann : 
        bops_id_equals_ann 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. apply bops_add_ann_add_id_id_equals_ann. 
       apply brel_set_reflexive; auto.
       exists nil; split. 
       apply bop_union_nil_is_id; auto. 
       apply bop_lift_nil_is_ann; auto.       
Defined.

End UnionIntersect.








