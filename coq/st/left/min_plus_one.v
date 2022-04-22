Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.nat.

Require Import CAS.coq.bs.min_plus.

Require Import CAS.coq.tr.left.plus_one.
Require Import CAS.coq.st.properties.
Require Import CAS.coq.st.structures.
From Coq Require Import Lia.
Section Theory.

Open Scope nat.

(* (a + 1) + (b min c) = ((a + 1)  + b) min ((a + 1) + c) *) 
Lemma slt_min_plus_one_distributive :
  slt_distributive brel_eq_nat bop_min ltr_plus_one. 
Proof. unfold slt_distributive. intros s t u.
       apply bop_min_plus_left_distributive. 
Qed.        

(* absorption *) 

Lemma min_plus_one_slt_absorptive : 
       slt_absorptive brel_eq_nat bop_min ltr_plus_one. 
Proof. unfold slt_absorptive. intros s t. unfold ltr_plus_one. 
       apply bops_min_plus_left_right_absorptive.
Qed. 

Lemma ltr_plus_one_increasing (s t : nat) : bop_min t (ltr_plus_one s t) = t.
Proof.  unfold bop_min. unfold ltr_plus_one. unfold bop_plus. 
       rewrite Min.min_comm.
       eapply min_add.
Qed. 

Lemma ltr_plus_one_strictly_increasing (s t : nat) : brel_eq_nat (ltr_plus_one s t) t = false. 
Proof.
  unfold brel_eq_nat, ltr_plus_one,
    bop_plus.
  eapply PeanoNat.Nat.eqb_neq.
  lia.
Qed.


Lemma min_plus_one_slt_strictly_absorptive : 
       slt_strictly_absorptive brel_eq_nat bop_min ltr_plus_one. 
Proof. unfold slt_strictly_absorptive. intros s t. split. 
       + apply min_plus_one_slt_absorptive. 
       + rewrite ltr_plus_one_increasing.
         rewrite ltr_plus_one_strictly_increasing; auto. 
Qed. 
End Theory.

Section ACAS.
  

End ACAS.

