Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.nat.

Require Import CAS.coq.bs.min_plus.

Require Import CAS.coq.tr.left.plus_one.
Require Import CAS.coq.st.properties.
Require Import CAS.coq.st.structures.
Require Import CAS.coq.sg.cast_up
  CAS.coq.sg.min.
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
  
(* 
       I need to build left pre semiring
*)

  
  Definition A_left_semiring_proof : @A_left_pre_semiring nat nat.
  Proof.
    econstructor.
    + 
      instantiate (1 := bop_min).
      instantiate (1 := A_eqv_nat).
      exact (A_sg_C_proofs_from_sg_CS_proofs 
        nat (A_eqv_eq nat A_eqv_nat) bop_min O S
        brel_eq_nat_not_trivial
        eqv_proofs_eq_nat
        min.sg_CS_proofs_min).
    +
      instantiate (1 := ltr_plus_one).
      instantiate (1 := A_eqv_nat).
      exact ltr_plus_one_proofs.
    + 
      unfold properties.bop_exists_ann_decidable.
      left;
      exact bop_min_exists_ann.
    + Search slt_exists_id_ann_decidable.
      constructor; split.
      eapply bop_min_not_exists_id.
      eapply ltr_plus_one_not_exists_ann.
    + 
      (* I realised that I need to discharge 
        slt_not_absorptive (A_eqv_eq nat A_eqv_nat) bop_min ltr_plus_one
        but Tim has proved that 
        slt_strictly_absorptive brel_eq_nat bop_min ltr_plus_one. 
        So, I need to add another record in structures.v file 
        
        Record left_pre_semiring_proofs {L S : Type} (r : brel S) 
        (add : binary_op S) (ltr : ltr_type L S) :=
        {
          A_left_pre_semiring_distributive  : slt_distributive r add ltr
        ; A_left_pre_semiring_strictly_absorptive : slt_strictly_absorptive brel_eq_nat bop_min ltr_plus_one                                              
        }.

        But this one appears to be after left semiring and before left_dioid but I could be wrong.

      *)
      constructor. 
      eapply slt_min_plus_one_distributive.
      
  Admitted.
    
End ACAS.



