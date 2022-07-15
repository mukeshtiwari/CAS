Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.

Require Import CAS.coq.eqv.bool. 
Require Import CAS.coq.sg.or.
Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.cast_up. 

Section Theory.

Lemma bops_and_or_left_distributive  : 
     bop_left_distributive bool brel_eq_bool bop_and bop_or. 
Proof. intros x y z. destruct x; destruct y; destruct z; compute; reflexivity. Qed. 

Lemma bops_and_or_right_distributive  : 
     bop_right_distributive bool brel_eq_bool bop_and bop_or.
Proof. intros x y z. destruct x; destruct y; destruct z; compute; reflexivity. Qed. 

Lemma bops_and_or_left_left_absorptive  : 
     bops_left_left_absorptive bool brel_eq_bool bop_and bop_or.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 

Lemma bops_and_or_left_right_absorptive  : 
     bops_left_right_absorptive bool brel_eq_bool bop_and bop_or.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 

Lemma bops_and_or_not_strictly_left_right_absorptive  : 
     bops_not_strictly_left_right_absorptive bool brel_eq_bool bop_and bop_or.
Proof. exists (true, true). compute. right. auto. Defined. 

Lemma bops_and_or_right_left_absorptive  : 
     bops_right_left_absorptive bool brel_eq_bool bop_and bop_or.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 

Lemma bops_and_or_right_right_absorptive  : 
     bops_right_right_absorptive bool brel_eq_bool bop_and bop_or.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 


Lemma bops_and_or_id_equals_ann : bops_exists_id_ann_equal bool brel_eq_bool bop_and bop_or. 
Proof. exists true. split. apply bop_and_true_is_id. apply bop_or_true_is_ann. Defined. 

Lemma bops_and_or_ann_equals_id : bops_exists_id_ann_equal bool brel_eq_bool bop_or bop_and.
Proof. exists false. split. apply bop_or_false_is_id. apply bop_and_false_is_ann. Defined.

Lemma bops_or_and_left_left_absorptive  : 
     bops_left_left_absorptive bool brel_eq_bool bop_or bop_and.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 
  
(* anti absorption *)
Lemma bops_or_and_not_left_anti_absorptive :
  bops_not_left_anti_absorptive bool brel_eq_bool bop_or bop_and.
Proof.
  unfold bops_not_left_anti_absorptive.
  compute.
  exists (true, true).
  reflexivity.
Defined.


Lemma bops_or_and_not_right_anti_absorptive :
  bops_not_right_anti_absorptive bool brel_eq_bool bop_or bop_and.
Proof.
  unfold bops_not_right_anti_absorptive.
  compute.
  exists (true, true).
  reflexivity.
Defined.

(*end of anti absorption *)

End Theory.

Section ACAS.


Definition distributive_lattice_proofs_and_or : distributive_lattice_proofs bool  brel_eq_bool bop_and bop_or := 
  {|
     A_distributive_lattice_absorptive        := bops_and_or_left_left_absorptive
   ; A_distributive_lattice_absorptive_dual   := bops_or_and_left_left_absorptive                                                 
   ; A_distributive_lattice_distributive      := bops_and_or_left_distributive
  |}.


Definition A_selective_distributive_lattice_and_or : A_selective_distributive_lattice bool := 
{|
  A_selective_distributive_lattice_eqv           := A_eqv_bool
; A_selective_distributive_lattice_join          := bop_and
; A_selective_distributive_lattice_meet          := bop_or
; A_selective_distributive_lattice_join_proofs   := A_sg_BCS_proofs _ A_sg_and
; A_selective_distributive_lattice_meet_proofs   := A_sg_BCS_proofs _ A_sg_or
; A_selective_distributive_lattice_id_ann_proofs := 
    {|
        A_bounded_plus_id_is_times_ann := bops_and_or_id_equals_ann  
      ; A_bounded_times_id_is_plus_ann := bops_and_or_ann_equals_id
    |}    
; A_selective_distributive_lattice_proofs        := distributive_lattice_proofs_and_or
; A_selective_distributive_lattice_ast           := Ast_and_or 
|}.

End ACAS.

Section AMCAS.

Definition A_mcas_bs_and_or := A_BS_selective_distributive_lattice _   A_selective_distributive_lattice_and_or.
  
End AMCAS.   

Section CAS.

Definition distributive_lattice_certs_and_or : @distributive_lattice_certificates bool := 
  {| 
     distributive_lattice_distributive      := Assert_Left_Distributive 
   ; distributive_lattice_absorptive_dual   := Assert_Left_Left_Absorptive_Dual
   ; distributive_lattice_absorptive        := Assert_Left_Left_Absorptive
  |}. 

Definition selective_distributive_lattice_and_or : @selective_distributive_lattice bool := 
{|
  selective_distributive_lattice_eqv          := eqv_bool 
; selective_distributive_lattice_join         := bop_and
; selective_distributive_lattice_meet        := bop_or
; selective_distributive_lattice_join_certs  := sg_BCS_certs sg_and
; selective_distributive_lattice_meet_certs  := sg_BCS_certs sg_or
; selective_distributive_lattice_id_ann_certs := 
    {|
        bounded_plus_id_is_times_ann := Assert_Exists_Id_Ann_Equal true
      ; bounded_times_id_is_plus_ann := Assert_Exists_Id_Ann_Equal false
    |}    
; selective_distributive_lattice_certs       := distributive_lattice_certs_and_or
; selective_distributive_lattice_ast         := Ast_and_or
|}.



End CAS.

Section MCAS.

Definition mcas_bs_and_or := BS_selective_distributive_lattice selective_distributive_lattice_and_or.
  
End MCAS.   


Section Verify.

Theorem correct_selective_distributive_lattice_and_or :
      selective_distributive_lattice_and_or = A2C_selective_distributive_lattice bool (A_selective_distributive_lattice_and_or). 
Proof. compute. reflexivity. Qed. 

Theorem correct_mcas_bs_and_or : mcas_bs_and_or = A2C_mcas_bs bool A_mcas_bs_and_or.
Proof. compute. reflexivity. Qed. 

 
End Verify.   
  
