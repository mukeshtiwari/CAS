Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.nat.

Require Import CAS.coq.bs.min_plus.

Require Import CAS.coq.tr.left.plus_one.
Require Import CAS.coq.st.properties.
Require Import CAS.coq.st.structures.

Section Theory.

Open Scope nat.

(* (a + 1) + (b min c) = ((a + 1)  + b) min ((a + 1) + c) *) 
Lemma slt_min_plus_one_distributive :
  slt_distributive nat nat brel_eq_nat bop_min ltr_plus_one. 
Proof. unfold slt_distributive. intros s t u.
       apply bop_min_plus_left_distributive. 
Qed.        

(* absorption *) 

Lemma min_plus_one_slt_absorptive : 
       slt_absorptive nat nat brel_eq_nat bop_min ltr_plus_one. 
Proof. unfold slt_absorptive. intros s t. unfold ltr_plus_one. 
       apply bops_min_plus_left_right_absorptive.
Qed. 

Lemma min_plus_one_slt_strictly_absorptive : 
       slt_strictly_absorptive nat nat brel_eq_nat bop_min ltr_plus_one. 
Proof. unfold slt_strictly_absorptive. intros s t. split. 
       + apply min_plus_one_slt_absorptive. 
       + unfold ltr_plus_one. 
         induction t.
         ++ compute. reflexivity. 
         ++ admit. 
Admitted. 


End Theory.

Section ACAS.
Open Scope nat.


End ACAS.

