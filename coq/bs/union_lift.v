Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.add_ann.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.bs.add_ann_add_id.
Require Import CAS.coq.bs.add_id_add_ann. 


Section Theory.
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
Defined. 

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
Defined. 


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
Defined. 


Lemma bops_union_lift_right_right_absorptive_raw : 
        bop_is_right S r bS -> bops_right_right_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros IR. 
       apply bops_left_right_absorptive_implies_right_right.
       apply brel_set_transitive; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bops_union_lift_left_right_absorptive_raw; auto. 
Defined. 

Lemma bops_union_lift_not_right_right_absorptive_raw : 
        bop_not_is_right S r bS -> bops_not_right_right_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros NIR. 
       apply bops_not_left_right_absorptive_implies_not_right_right.
       apply brel_set_transitive; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bops_union_lift_not_left_right_absorptive_raw; auto. 
Defined. 



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
Defined. 


Lemma bops_union_lift_left_distributive_decide :
        bop_is_left_decidable S r bS -> 
        bop_left_distributive_decidable  
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intros [IL | NIL].
       left. apply bops_union_lift_left_distributive; auto. 
       right. apply bops_union_lift_not_left_distributive; auto.
Defined. 

Lemma bops_union_lift_right_distributive :
        bop_is_right S r bS -> (*********** NB ************)
        bop_right_distributive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intro IL.
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
Defined. 

Lemma bops_union_lift_right_distributive_decide :
        bop_is_right_decidable S r bS -> 
        bop_right_distributive_decidable  
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intros [IL | NIL].
       left. apply bops_union_lift_right_distributive; auto. 
       right. apply bops_union_lift_not_right_distributive; auto.
Defined. 



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
Defined. 

Lemma bops_union_lift_left_left_absorptive_decide :
        bop_is_left_decidable S r bS -> 
        bops_left_left_absorptive_decidable  
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intros [L | R].
       left. apply bops_union_lift_left_left_absorptive; auto. 
       right. apply bops_union_lift_not_left_left_absorptive; auto.
Defined. 




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
Defined. 

Lemma bops_union_lift_left_right_absorptive_decide :
        bop_is_right_decidable S r bS -> 
        bops_left_right_absorptive_decidable  
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intros [L | R].
       left. apply bops_union_lift_left_right_absorptive; auto. 
       right. apply bops_union_lift_not_left_right_absorptive; auto.
Defined. 


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
Defined. 

Lemma bops_union_lift_right_left_absorptive_decide :
        bop_is_left_decidable S r bS -> 
        bops_right_left_absorptive_decidable  
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intros [L | R].
       left. apply bops_union_lift_right_left_absorptive; auto. 
       right. apply bops_union_lift_not_right_left_absorptive; auto.
Defined. 


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
Defined. 

Lemma bops_union_lift_right_right_absorptive_decide :
        bop_is_right_decidable S r bS -> 
        bops_right_right_absorptive_decidable  
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_lift r bS) c). 
Proof. intros [L | R].
       left. apply bops_union_lift_right_right_absorptive; auto. 
       right. apply bops_union_lift_not_right_right_absorptive; auto.
Defined. 


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

End Theory. 

Section ACAS.



Definition bs_proofs_union_lift : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
     eqv_proofs S rS -> 
     sg_proofs S rS bS -> 
        bs_proofs 
           (with_constant (finite_set S)) 
           (brel_add_constant (brel_set rS) c)
           (bop_add_ann (bop_union rS) c)
           (bop_add_id (bop_lift rS bS) c) 
:= λ S rS c bS eqvS sgS,
let refS := A_eqv_reflexive S rS eqvS  in
let symS := A_eqv_symmetric S rS eqvS  in
let trnS := A_eqv_transitive S rS eqvS in
let cnbS := A_sg_congruence S rS bS sgS in
let ilD  := A_sg_is_left_d S rS bS sgS  in
let irD  := A_sg_is_right_d S rS bS sgS in 
{|
  A_bs_left_distributive_d      := bops_union_lift_left_distributive_decide S rS bS refS symS trnS cnbS c ilD 
; A_bs_right_distributive_d     := bops_union_lift_right_distributive_decide S rS bS refS symS trnS cnbS c irD 
; A_bs_left_left_absorptive_d   := bops_union_lift_left_left_absorptive_decide S rS bS refS symS trnS cnbS c ilD 
; A_bs_left_right_absorptive_d  := bops_union_lift_left_right_absorptive_decide S rS bS refS symS trnS cnbS c irD 
; A_bs_right_left_absorptive_d  := bops_union_lift_right_left_absorptive_decide S rS bS refS symS trnS cnbS c ilD 
; A_bs_right_right_absorptive_d := bops_union_lift_right_right_absorptive_decide S rS bS refS symS trnS cnbS c irD 
; A_bs_plus_id_is_times_ann_d   := inl (bops_union_lift_id_equals_ann S rS bS refS symS trnS c)
; A_bs_times_id_is_plus_ann_d   := inl (bops_union_lift_ann_equals_id S rS bS refS symS c)
|}. 


Definition A_bs_CI_union_lift : ∀ (S : Type),  A_sg S -> cas_constant -> A_bs_CI (with_constant (finite_set S)) 
:= λ S sgS c,
let eqvS  := A_sg_eq S sgS in
let rS    := A_eqv_eq S eqvS in   
let bS    := A_sg_bop S sgS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
{| 
     A_bs_CI_eqv          := A_eqv_add_constant (finite_set S) (A_eqv_set S eqvS) c 
   ; A_bs_CI_plus         := bop_add_ann (bop_union rS) c
   ; A_bs_CI_times        := bop_add_id (bop_lift rS bS) c
   ; A_bs_CI_plus_proofs  := sg_CI_proofs_union S rS c s f Pf peqvS
   ; A_bs_CI_times_proofs := sg_proofs_add_id (finite_set S) (brel_set rS) c
                                           (bop_lift rS bS) (nil) 
                                           (λ (l : finite_set S), if brel_set rS nil l then (s :: nil) else nil)
                                           (brel_set_not_trivial S rS s)
                                           (eqv_proofs_set S rS peqvS)
                                           (sg_lift_proofs S rS bS peqvS s f Pf (A_eqv_exactly_two_d S eqvS) (A_sg_proofs S sgS)) 
   ; A_bs_CI_proofs       := bs_proofs_union_lift S rS c bS peqvS (A_sg_proofs S sgS)
   ; A_bs_CI_plus_ast     := Ast_bop_add_ann(c, Ast_bop_union (A_eqv_ast S eqvS))
   ; A_bs_CI_times_ast    := Ast_bop_add_id(c, Ast_bop_lift (A_sg_bop_ast S sgS))                                            
   ; A_bs_CI_ast          := Ast_bs_CI_union_lift (c, A_sg_ast S sgS)
|}.


  
End ACAS.

Section CAS.


Definition bops_union_lift_left_distributive_check {S : Type} (c : cas_constant) (ilD : @check_is_left S) :
    @check_left_distributive (with_constant (finite_set S)) :=
match ilD with
| Certify_Is_Left => Certify_Left_Distributive
| Certify_Not_Is_Left (s1, s2) => Certify_Not_Left_Distributive (inr (s1 :: nil), (inl c, inr (s2 :: nil)))
end. 

Definition bops_union_lift_right_distributive_check {S : Type} (c : cas_constant) (ilD : @check_is_right S) :
    @check_right_distributive (with_constant (finite_set S)) :=
match ilD with
| Certify_Is_Right => Certify_Right_Distributive
| Certify_Not_Is_Right (s1, s2) => Certify_Not_Right_Distributive (inr (s2 :: nil), (inl c, inr (s1 :: nil)))
end. 


Definition bops_union_lift_left_left_absorptive_check {S : Type} (ilD : @check_is_left S) :
    @check_left_left_absorptive (with_constant (finite_set S)) :=
match ilD with
| Certify_Is_Left              => Certify_Left_Left_Absorptive
| Certify_Not_Is_Left (s1, s2) => Certify_Not_Left_Left_Absorptive (inr (s1 :: nil), inr (s2 :: nil))
end. 

Definition bops_union_lift_left_right_absorptive_check {S : Type} (ilD : @check_is_right S) :
    @check_left_right_absorptive (with_constant (finite_set S)) :=
match ilD with
| Certify_Is_Right              => Certify_Left_Right_Absorptive
| Certify_Not_Is_Right (s1, s2) => Certify_Not_Left_Right_Absorptive (inr (s2 :: nil), inr (s1 :: nil))
end. 


Definition bops_union_lift_right_left_absorptive_check {S : Type} (ilD : @check_is_left S) :
    @check_right_left_absorptive (with_constant (finite_set S)) :=
match ilD with
| Certify_Is_Left              => Certify_Right_Left_Absorptive
| Certify_Not_Is_Left (s1, s2) => Certify_Not_Right_Left_Absorptive (inr (s1 :: nil), inr (s2 :: nil))
end. 

Definition bops_union_lift_right_right_absorptive_check {S : Type} (ilD : @check_is_right S) :
    @check_right_right_absorptive (with_constant (finite_set S)) :=
match ilD with
| Certify_Is_Right              => Certify_Right_Right_Absorptive
| Certify_Not_Is_Right (s1, s2) => Certify_Not_Right_Right_Absorptive (inr (s2 :: nil), inr (s1 :: nil))
end. 


Definition bs_certs_union_lift : 
  ∀ {S : Type} (c : cas_constant), @sg_certificates S -> @bs_certificates (with_constant (finite_set S)) 
:= λ S c sgS,
{|
  bs_left_distributive_d      := bops_union_lift_left_distributive_check c (sg_is_left_d sgS)
; bs_right_distributive_d     := bops_union_lift_right_distributive_check c (sg_is_right_d sgS)
; bs_left_left_absorptive_d   := bops_union_lift_left_left_absorptive_check (sg_is_left_d sgS)
; bs_left_right_absorptive_d  := bops_union_lift_left_right_absorptive_check (sg_is_right_d sgS)
; bs_right_left_absorptive_d  := bops_union_lift_right_left_absorptive_check (sg_is_left_d sgS)
; bs_right_right_absorptive_d := bops_union_lift_right_right_absorptive_check (sg_is_right_d sgS)
; bs_plus_id_is_times_ann_d   := Certify_Plus_Id_Equals_Times_Ann 
; bs_times_id_is_plus_ann_d   := Certify_Times_Id_Equals_Plus_Ann 
|}.


Definition bs_CI_union_lift : ∀ (S : Type),  @sg S -> cas_constant -> @bs_CI (with_constant (finite_set S)) 
:= λ S sgS c,
let eqvS  := sg_eq sgS in
let rS    := eqv_eq eqvS in   
let bS    := sg_bop sgS in
let s     := eqv_witness eqvS in
let f     := eqv_new eqvS in
{| 
     bs_CI_eqv         := eqv_add_constant (eqv_set eqvS) c 
   ; bs_CI_plus        := bop_add_ann (bop_union rS) c
   ; bs_CI_times       := bop_add_id (bop_lift rS bS) c
   ; bs_CI_plus_certs  := sg_CI_certs_union c s f 
   ; bs_CI_times_certs := sg_certs_add_id c nil 
                                           (λ (l : finite_set S), if brel_set rS nil l then (s :: nil) else nil)
                                           (sg_lift_certs S rS s f (eqv_exactly_two_d eqvS) bS (sg_certs sgS)) 
   ; bs_CI_certs       := bs_certs_union_lift c (sg_certs sgS)
   ; bs_CI_plus_ast    := Ast_bop_add_ann(c, Ast_bop_union (eqv_ast eqvS))
   ; bs_CI_times_ast   := Ast_bop_add_id(c, Ast_bop_lift (sg_bop_ast sgS))
   ; bs_CI_ast         := Ast_bs_CI_union_lift (c, sg_ast sgS)
|}.


End CAS.

Section Verify.


Lemma correct_bops_union_lift_left_distributive_check 
  (S : Type)
  (c : cas_constant)
  (eq : brel S)
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (il_d : bop_is_left_decidable S eq bS) : 
   p2c_left_distributive (with_constant (finite_set S))
                         (brel_add_constant (brel_set eq) c)
                         (bop_add_ann (bop_union eq) c)
                         (bop_add_id (bop_lift eq bS) c)
                         (bops_union_lift_left_distributive_decide S eq bS refS symS trnS cong c il_d)
   =
   bops_union_lift_left_distributive_check c (p2c_is_left_check S eq bS il_d). 
Proof. destruct il_d as [IL | [ [s1 s2] NIL ]]; simpl; reflexivity. Qed. 

Lemma correct_bops_union_lift_right_distributive_check 
  (S : Type)
  (c : cas_constant)
  (eq : brel S)
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (ir_d : bop_is_right_decidable S eq bS):
  p2c_right_distributive (with_constant (finite_set S))
                         (brel_add_constant (brel_set eq) c)
                         (bop_add_ann (bop_union eq) c)
                         (bop_add_id (bop_lift eq bS) c)
                         (bops_union_lift_right_distributive_decide S eq bS refS symS trnS cong c ir_d)
  =                          
  bops_union_lift_right_distributive_check c (p2c_is_right_check S eq bS ir_d). 
Proof. destruct ir_d as [IR | [ [s1 s2] NIR ]]; simpl; reflexivity. Qed. 

Lemma correct_bops_union_lift_left_left_absorptive_check 
  (S : Type)
  (c : cas_constant)
  (eq : brel S)
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (il_d : bop_is_left_decidable S eq bS) : 
  p2c_left_left_absorptive (with_constant (finite_set S))
                           (brel_add_constant (brel_set eq) c)
                           (bop_add_ann (bop_union eq) c)
                           (bop_add_id (bop_lift eq bS) c)
                           (bops_union_lift_left_left_absorptive_decide S eq bS refS symS trnS cong c il_d)
  =                                                                               
  bops_union_lift_left_left_absorptive_check (p2c_is_left_check S eq bS il_d).
Proof. destruct il_d as [IL | [ [s1 s2] NIL ]]; simpl; reflexivity. Qed. 

Lemma correct_bops_union_lift_left_right_absorptive_check 
  (S : Type)
  (c : cas_constant)
  (eq : brel S)
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (ir_d : bop_is_right_decidable S eq bS):
  p2c_left_right_absorptive (with_constant (finite_set S))
                            (brel_add_constant (brel_set eq) c)
                            (bop_add_ann (bop_union eq) c)
                            (bop_add_id (bop_lift eq bS) c)
                            (bops_union_lift_left_right_absorptive_decide S eq bS refS symS trnS cong c ir_d)
  =
  bops_union_lift_left_right_absorptive_check (p2c_is_right_check S eq bS ir_d).
Proof. destruct ir_d as [IR | [ [s1 s2] NIR ]]; simpl; reflexivity. Qed. 

Lemma correct_bops_union_lift_right_left_absorptive_check 
  (S : Type)
  (c : cas_constant)
  (eq : brel S)
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (il_d : bop_is_left_decidable S eq bS) : 
  p2c_right_left_absorptive (with_constant (finite_set S))
                            (brel_add_constant (brel_set eq) c)
                            (bop_add_ann (bop_union eq) c)
                            (bop_add_id (bop_lift eq bS) c)
                            (bops_union_lift_right_left_absorptive_decide S eq bS refS symS trnS cong c il_d)
  =
  bops_union_lift_right_left_absorptive_check (p2c_is_left_check S eq bS il_d).
Proof. destruct il_d as [IL | [ [s1 s2] NIL ]]; simpl; reflexivity. Qed. 

Lemma correct_bops_union_lift_right_right_absorptive_check 
  (S : Type)
  (c : cas_constant)
  (eq : brel S)
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (ir_d : bop_is_right_decidable S eq bS):
  p2c_right_right_absorptive (with_constant (finite_set S))
                             (brel_add_constant (brel_set eq) c)
                             (bop_add_ann (bop_union eq) c) (bop_add_id (bop_lift eq bS) c)
                             (bops_union_lift_right_right_absorptive_decide S eq bS refS symS trnS cong c ir_d) 
  =                                      
  bops_union_lift_right_right_absorptive_check (p2c_is_right_check S eq bS ir_d). 
Proof. destruct ir_d as [IR | [ [s1 s2] NIR ]]; simpl; reflexivity. Qed. 

Lemma correct_bs_certs_union_lift 
  (S : Type)
  (c : cas_constant)    
  (eq : brel S)
  (bS : binary_op S)
  (eqvP : eqv_proofs S eq) 
  (sgP : sg_proofs S eq bS) : 
  P2C_bs (with_constant (finite_set S))
                        (brel_add_constant (brel_set eq) c)
                        (bop_add_ann (bop_union eq) c)
                        (bop_add_id (bop_lift eq bS) c)
                        (bs_proofs_union_lift S eq c bS eqvP sgP)
  = 
  bs_certs_union_lift c (P2C_sg S eq bS sgP).
Proof. destruct sgP. unfold bs_proofs_union_lift, bs_certs_union_lift, P2C_sg, P2C_bs; simpl. 
       rewrite correct_bops_union_lift_left_distributive_check.
       rewrite correct_bops_union_lift_right_distributive_check.
       rewrite correct_bops_union_lift_left_left_absorptive_check.
       rewrite correct_bops_union_lift_left_right_absorptive_check.
       rewrite correct_bops_union_lift_right_left_absorptive_check .
       rewrite correct_bops_union_lift_right_right_absorptive_check.
       reflexivity. 
Qed.   

    

Theorem correct_bs_union_lift : ∀ (S : Type) (sgS: A_sg S) (c : cas_constant), 
   bs_CI_union_lift S (A2C_sg S sgS) c 
   =
   A2C_bs_CI (with_constant (finite_set S)) (A_bs_CI_union_lift S sgS c). 
Proof. intros S sgS c. 
       unfold bs_CI_union_lift, A_bs_CI_union_lift, A2C_bs_CI, A2C_sg. destruct sgS. simpl. 
       rewrite <- correct_eqv_add_constant. 
       rewrite <- bop_union_certs_correct. 
       rewrite <- correct_sg_certs_add_id.
       rewrite correct_bs_certs_union_lift.        

       (* hmmm. need some abstraction here for composition of certs/proofs ... *) 
       unfold sg_certs_add_id; destruct A_sg_proofs; destruct A_sg_eq; simpl. 
       unfold P2C_sg. unfold bs_certs_union_lift. simpl.
       destruct A_sg_commutative_d as [C | [[s1 s2] NC] ] ;
       destruct A_sg_is_left_d as [IL | [[s3 s4] NIL]] ;
       destruct A_sg_idempotent_d as [I | [s5 NI]];
       destruct A_sg_is_right_d as [IR | [[s6 s7] NIR]];
       destruct A_sg_selective_d as [SL | [ [s8 s9] NSL ] ];
       destruct A_eqv_exactly_two_d as [ [[s10 s11] EX2] | [g NEX2] ] ;
       simpl; simpl in *; try reflexivity.    
Qed. 

End Verify. 










