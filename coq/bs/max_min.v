
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.nat.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.max.
Require Import CAS.coq.sg.min.
Require Import CAS.coq.sg.cast_up.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory. 
Require Import CAS.coq.bs.min_max. (* for bops_min_max_left_left_absorptive *) 

Section Theory.

Lemma bops_max_min_left_left_absorptive  : 
     bops_left_left_absorptive nat brel_eq_nat bop_max bop_min. 
Proof. unfold bops_left_left_absorptive. 
       induction s; induction t; simpl; auto. 
       apply brel_eq_nat_reflexive. 
Qed.

Lemma bops_max_min_left_right_absorptive  : 
       bops_left_right_absorptive nat brel_eq_nat bop_max bop_min. 
Proof. apply bops_left_left_absorptive_implies_left_right.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_max_congruence. 
       apply bop_min_commutative. 
       apply bops_max_min_left_left_absorptive. 
Qed. 


Lemma bops_max_min_right_left_absorptive  : 
       bops_right_left_absorptive nat brel_eq_nat bop_max bop_min. 
Proof. apply bops_left_right_absorptive_implies_right_left.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_max_congruence. 
       apply bop_max_commutative. 
       apply bop_min_commutative. 
       apply bops_max_min_left_right_absorptive. 
Qed. 



Lemma bops_max_min_right_right_absorptive  : 
       bops_right_right_absorptive nat brel_eq_nat bop_max bop_min. 
Proof. apply bops_right_left_absorptive_implies_right_right.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_max_congruence. 
       apply bop_min_commutative. 
       apply bops_max_min_right_left_absorptive. 
Qed. 


Lemma bops_max_min_left_distributive  : 
     bop_left_distributive nat brel_eq_nat bop_max bop_min. 
Proof. unfold bop_left_distributive. 
       induction s; induction t; induction u; simpl; auto. 
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_symmetric. 
       apply brel_eq_nat_reflexive. 
Qed. 

Lemma bops_max_min_right_distributive  : 
     bop_right_distributive nat brel_eq_nat bop_max bop_min. 
Proof. apply bop_left_distributive_implies_right. 
       exact brel_eq_nat_transitive. 
       exact bop_max_congruence. 
       exact bop_max_commutative. 
       exact bop_min_commutative. 
       exact bops_max_min_left_distributive. 
Qed. 

Open Scope nat.


Lemma bops_id_equals_ann_max_min : bops_exists_id_ann_equal nat brel_eq_nat bop_max bop_min.
Proof. exists 0. split. apply bop_max_zero_is_id. apply bop_min_zero_is_ann.  Defined.

End Theory.

Section ACAS.

Open Scope nat.


Definition id_ann_proofs_max_min : pid_is_tann_proofs nat brel_eq_nat bop_max bop_min := 
{|
   A_pid_is_tann_plus_times   := bops_id_equals_ann_max_min
 ; A_pid_is_tann_times_plus_d := Id_Ann_Proof_None _ _ _ _ (bop_min_not_exists_id, bop_max_not_exists_ann)
|}. 


Definition distributive_lattice_proofs_max_min : distributive_lattice_proofs nat brel_eq_nat bop_max bop_min := 
{|
    A_distributive_lattice_absorptive      := bops_max_min_left_left_absorptive
  ; A_distributive_lattice_absorptive_dual := bops_min_max_left_left_absorptive
  ; A_distributive_lattice_distributive    := bops_max_min_left_distributive
|}.

Definition A_max_min : A_selective_distributive_prelattice_with_zero  nat  := 
{|
  A_selective_distributive_prelattice_with_zero_eqv           := A_eqv_nat
; A_selective_distributive_prelattice_with_zero_join          := bop_max
; A_selective_distributive_prelattice_with_zero_meet          := bop_min
; A_selective_distributive_prelattice_with_zero_join_proofs   := sg_CS_proofs_max
; A_selective_distributive_prelattice_with_zero_meet_proofs   := sg_CS_proofs_min
; A_selective_distributive_prelattice_with_zero_id_ann_proofs := id_ann_proofs_max_min                                                                  
; A_selective_distributive_prelattice_with_zero_proofs        := distributive_lattice_proofs_max_min
; A_selective_distributive_prelattice_with_zero_ast           := Ast_max_min
|}.


End ACAS.

Section CAS.
Open Scope nat.


Definition id_ann_certs_max_min : @pid_is_tann_certificates nat := 
{|
   pid_is_tann_plus_times   := Assert_Exists_Id_Ann_Equal 0 
 ; pid_is_tann_times_plus_d := Id_Ann_Cert_None
|}. 


Definition distributive_lattice_certs_max_min : @distributive_lattice_certificates nat := 
{|
    distributive_lattice_absorptive       := Assert_Left_Left_Absorptive
  ; distributive_lattice_absorptive_dual := Assert_Left_Left_Absorptive_Dual
  ; distributive_lattice_distributive    := Assert_Left_Distributive
|}.

Definition max_min : @selective_distributive_prelattice_with_zero  nat  :=
{|
  selective_distributive_prelattice_with_zero_eqv          := eqv_eq_nat
; selective_distributive_prelattice_with_zero_join         := bop_max
; selective_distributive_prelattice_with_zero_meet         := bop_min
; selective_distributive_prelattice_with_zero_join_certs   := sg_CS_certs_max
; selective_distributive_prelattice_with_zero_meet_certs   := sg_CS_certs_min
; selective_distributive_prelattice_with_zero_id_ann_certs := id_ann_certs_max_min                                                                  
; selective_distributive_prelattice_with_zero_certs        := distributive_lattice_certs_max_min
; selective_distributive_prelattice_with_zero_ast          := Ast_max_min
|}.

End CAS.

Section Verify.

Theorem correct_max_min : max_min = A2C_selective_distributive_prelattice_with_zero nat A_max_min. 
Proof. compute. reflexivity. Qed. 


End Verify.   
  

