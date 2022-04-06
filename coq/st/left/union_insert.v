Require Import CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties. 
Require Import CAS.coq.eqv.set. 
Require Import CAS.coq.sg.union. 
Require Import CAS.coq.tr.left.insert.
Require Import CAS.coq.bs.properties. 
Require Import CAS.coq.st.properties. 
Require Import CAS.coq.st.structures.

Section Theory.

Variables (S : Type)
          (wS : S)   
          (eq : brel S)
          (ref : brel_reflexive S eq)
          (sym : brel_symmetric S eq)
          (trn : brel_transitive S eq). 

(* where does this belong? *) 
Lemma bops_union_union_left_distributive : bop_left_distributive (finite_set S) (brel_set eq) (bop_union eq) (bop_union eq). 
Proof. intros Z X Y.
       apply brel_set_intro_prop; auto. split.
       + intros s A.
         apply in_set_bop_union_elim in A; auto.
         apply in_set_bop_union_intro; auto.
         destruct A as [A | A].
         ++ left. apply in_set_bop_union_intro; auto.
         ++ apply in_set_bop_union_elim in A; auto.
            destruct A as [A | A].
            +++ left. apply in_set_bop_union_intro; auto.
            +++ right. apply in_set_bop_union_intro; auto.
       + intros s A.
         apply in_set_bop_union_elim in A; auto.
         apply in_set_bop_union_intro; auto.
         destruct A as [A | A].
         ++ apply in_set_bop_union_elim in A; auto.
            destruct A as [A | A].
            +++ left. exact A. 
            +++ right. apply in_set_bop_union_intro; auto.
         ++ apply in_set_bop_union_elim in A; auto.
            destruct A as [A | A].
            +++ left. exact A. 
            +++ right. apply in_set_bop_union_intro; auto.
Qed. 


Lemma slt_union_insert_distributive : slt_distributive S (finite_set S) (brel_set eq) (bop_union eq) (ltr_insert eq).
Proof. intros s X Y. unfold slt_distributive, ltr_insert.
       (* need special case of Z U (X U Y) = (Z U X) U (Z U Y) *)
       apply bops_union_union_left_distributive. 
Qed. 

Lemma slt_union_insert_not_absorptive : 
       slt_not_absorptive S (finite_set S) (brel_set eq) (bop_union eq) (ltr_insert eq).
Proof. exists (wS, nil). compute. reflexivity. Defined. 

Lemma slt_union_insert_not_strictly_absorptive : 
       slt_not_strictly_absorptive S (finite_set S) (brel_set eq) (bop_union eq) (ltr_insert eq).
Proof. exists (wS, nil). left. compute. reflexivity. Defined. 


End Theory.   
