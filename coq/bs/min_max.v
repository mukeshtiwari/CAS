Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.nat.
Require Import CAS.coq.sg.properties.

Require Import CAS.coq.sg.max.
Require Import CAS.coq.sg.min.


Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory. 


Section Theory.

Lemma bops_min_max_left_left_absorptive  : 
     bops_left_left_absorptive nat brel_eq_nat bop_min bop_max. 
Proof. unfold bops_left_left_absorptive. 
       induction s; induction t; simpl; auto. 
       apply brel_eq_nat_symmetric. 
       apply bop_min_idempotent. 
Qed.

Lemma bops_max_min_left_left_absorptive  : 
     bops_left_left_absorptive nat brel_eq_nat bop_max bop_min. 
Proof. unfold bops_left_left_absorptive.
       induction s; induction t; simpl; auto. 
       apply brel_eq_nat_reflexive. 
Qed. 


(* strict absorption *)
Lemma bops_min_max_not_left_strictly_absorptive  : 
  bops_not_left_strictly_absorptive nat brel_eq_nat bop_min bop_max.
Proof.
  exists (0, 0)%nat.
  compute.
  right; auto.
Qed.

Lemma bops_min_max_not_right_strictly_absorptive  : 
  bops_not_right_strictly_absorptive nat brel_eq_nat bop_min bop_max.
Proof.
  exists (0, 0)%nat.
  compute.
  right; auto.
Qed.


Lemma bops_min_max_left_right_absorptive  : 
       bops_left_right_absorptive nat brel_eq_nat bop_min bop_max. 
Proof. apply bops_left_left_absorptive_implies_left_right.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_min_congruence. 
       apply bop_max_commutative. 
       apply bops_min_max_left_left_absorptive. 
Qed. 


Lemma bops_min_max_right_left_absorptive  : 
       bops_right_left_absorptive nat brel_eq_nat bop_min bop_max. 
Proof. apply bops_left_right_absorptive_implies_right_left.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_min_congruence. 
       apply bop_min_commutative. 
       apply bop_max_commutative. 
       apply bops_min_max_left_right_absorptive. 
Qed. 



Lemma bops_min_max_right_right_absorptive  : 
       bops_right_right_absorptive nat brel_eq_nat bop_min bop_max. 
Proof. apply bops_right_left_absorptive_implies_right_right.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_min_congruence. 
       apply bop_max_commutative. 
       apply bops_min_max_right_left_absorptive. 
Qed. 



Lemma bops_min_max_left_distributive  : 
     bop_left_distributive nat brel_eq_nat bop_min bop_max. 
Proof. unfold bop_left_distributive. 
       induction s; induction t; induction u; simpl; auto. 
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_symmetric. 
       apply bop_min_idempotent. 
       apply bops_min_max_left_left_absorptive. 
       assert (H := bop_min_commutative s (bop_max s t)). 
       assert (K : brel_eq_nat s (bop_min s (bop_max s t)) = true). 
          apply bops_min_max_left_left_absorptive. 
       assert (T := brel_eq_nat_transitive _ _ _ K H). 
       assumption. 
Qed. 

Lemma bops_min_max_right_distributive  : 
     bop_right_distributive nat brel_eq_nat bop_min bop_max. 
Proof. apply bop_left_distributive_implies_right. 
       exact brel_eq_nat_transitive. 
       exact bop_min_congruence. 
       exact bop_min_commutative. 
       exact bop_max_commutative. 
       exact bops_min_max_left_distributive. 
Qed. 

Open Scope nat.

Lemma bops_id_equals_ann_min_max : bops_exists_id_ann_equal nat brel_eq_nat bop_max bop_min. 
Proof. exists 0. split. apply bop_max_zero_is_id. apply bop_min_zero_is_ann.  Defined.

End Theory.

Section ACAS.

Open Scope nat.

Definition id_ann_proofs_min_max : pann_is_tid_proofs nat brel_eq_nat bop_min bop_max := 
{|
  A_pann_is_tid_plus_times_d   := Id_Ann_Proof_None _ _ _ _ (bop_min_not_exists_id, bop_max_not_exists_ann) 
; A_pann_is_tid_times_plus     := bops_id_equals_ann_min_max 
|}.


Definition distributive_lattice_proofs_min_max : distributive_lattice_proofs nat brel_eq_nat bop_min bop_max := 
{|
    A_distributive_lattice_absorptive      := bops_min_max_left_left_absorptive
  ; A_distributive_lattice_absorptive_dual := bops_max_min_left_left_absorptive
  ; A_distributive_lattice_distributive    := bops_min_max_left_distributive
|}.

Definition A_min_max : A_selective_distributive_prelattice_with_one  nat  := 
{|
  A_selective_distributive_prelattice_with_one_eqv           := A_eqv_nat
; A_selective_distributive_prelattice_with_one_join          := bop_min
; A_selective_distributive_prelattice_with_one_meet          := bop_max
; A_selective_distributive_prelattice_with_one_join_proofs   := sg_CS_proofs_min
; A_selective_distributive_prelattice_with_one_meet_proofs   := sg_CS_proofs_max
; A_selective_distributive_prelattice_with_one_id_ann_proofs := id_ann_proofs_min_max                                                                  
; A_selective_distributive_prelattice_with_one_proofs        := distributive_lattice_proofs_min_max
; A_selective_distributive_prelattice_with_one_ast           := Ast_min_max
|}.


End ACAS.

Section MACAS.

Definition A_mcas_min_max := A_BS_selective_distributive_prelattice_with_one _ A_min_max. 

End MACAS.


Section CAS.
Open Scope nat.

Definition id_ann_certs_min_max : @pann_is_tid_certificates nat := 
{|
   pann_is_tid_plus_times_d   := Id_Ann_Cert_None
 ; pann_is_tid_times_plus     := Assert_Exists_Id_Ann_Equal 0 
|}. 


Definition distributive_lattice_certs_min_max : @distributive_lattice_certificates nat := 
{|
    distributive_lattice_absorptive       := Assert_Left_Left_Absorptive
  ; distributive_lattice_absorptive_dual := Assert_Left_Left_Absorptive_Dual
  ; distributive_lattice_distributive    := Assert_Left_Distributive
|}.

Definition min_max : @selective_distributive_prelattice_with_one  nat  :=
{|
  selective_distributive_prelattice_with_one_eqv          := eqv_eq_nat
; selective_distributive_prelattice_with_one_join         := bop_min
; selective_distributive_prelattice_with_one_meet         := bop_max
; selective_distributive_prelattice_with_one_join_certs   := sg_CS_certs_max
; selective_distributive_prelattice_with_one_meet_certs   := sg_CS_certs_min
; selective_distributive_prelattice_with_one_id_ann_certs := id_ann_certs_min_max                                                                  
; selective_distributive_prelattice_with_one_certs        := distributive_lattice_certs_min_max
; selective_distributive_prelattice_with_one_ast          := Ast_min_max
|}.

End CAS.

Section MACAS.

Definition mcas_min_max := BS_selective_distributive_prelattice_with_one min_max. 

End MACAS.



Section Verify.

Theorem correct_min_max : min_max = A2C_selective_distributive_prelattice_with_one nat A_min_max. 
Proof. compute. reflexivity. Qed. 

Theorem correct_mcas_min_max : mcas_min_max = A2C_mcas_bs nat A_mcas_min_max.
Proof. compute. reflexivity. Qed. 


End Verify.   
  

