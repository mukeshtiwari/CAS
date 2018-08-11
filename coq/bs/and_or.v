Require Import CAS.coq.common.base.
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

Lemma bops_and_or_right_left_absorptive  : 
     bops_right_left_absorptive bool brel_eq_bool bop_and bop_or.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 

Lemma bops_and_or_right_right_absorptive  : 
     bops_right_right_absorptive bool brel_eq_bool bop_and bop_or.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 


Lemma bops_and_or_id_equals_ann : bops_id_equals_ann bool brel_eq_bool bop_and bop_or. 
Proof. exists true. split. apply bop_and_true_is_id. apply bop_or_true_is_ann. Defined. 

Lemma bops_and_or_ann_equals_id : bops_id_equals_ann bool brel_eq_bool bop_or bop_and.
Proof. exists false. split. apply bop_or_false_is_id. apply bop_and_false_is_ann. Defined.       
  
End Theory.

Section ACAS.

Lemma bops_or_and_left_left_absorptive  : 
     bops_left_left_absorptive bool brel_eq_bool bop_or bop_and.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 
  

Definition distributive_lattice_proofs_and_or : distributive_lattice_proofs bool  brel_eq_bool bop_and bop_or := 
  {|
     A_distributive_lattice_absorptive        := bops_and_or_left_left_absorptive
   ; A_distributive_lattice_absorptive_dual   := bops_or_and_left_left_absorptive                                                 
   ; A_distributive_lattice_distributive      := bops_and_or_left_distributive
  |}. 

Definition A_distributive_lattice_and_or : A_distributive_lattice bool := 
{|
  A_distributive_lattice_eqv          := A_eqv_bool
; A_distributive_lattice_join         := bop_and
; A_distributive_lattice_meet         := bop_or
; A_distributive_lattice_join_proofs  := A_sg_CI_proofs _ (A_sg_CI_from_sg_CS _ (A_sg_CS_and))
; A_distributive_lattice_meet_proofs  := A_sg_CI_proofs _ (A_sg_CI_from_sg_CS _ (A_sg_CS_or))
; A_distributive_lattice_proofs       := distributive_lattice_proofs_and_or
; A_distributive_lattice_ast          := Ast_distributive_lattice_and_or
|}.

End ACAS.

Section CAS.

Definition distributive_lattice_certs_and_or : @distributive_lattice_certificates bool := 
  {| 
     distributive_lattice_distributive      := Assert_Left_Distributive 
   ; distributive_lattice_absorptive_dual   := Assert_Left_Left_Absorptive_Dual
   ; distributive_lattice_absorptive        := Assert_Left_Left_Absorptive
  |}. 

Definition distributive_lattice_and_or : @distributive_lattice bool := 
{|
  distributive_lattice_eqv          := eqv_bool 
; distributive_lattice_join         := bop_and
; distributive_lattice_meet        := bop_or
; distributive_lattice_join_certs  := sg_CI_certs (sg_CI_from_sg_CS (sg_CS_and))
; distributive_lattice_meet_certs  := sg_CI_certs (sg_CI_from_sg_CS (sg_CS_or))
; distributive_lattice_certs       := distributive_lattice_certs_and_or
; distributive_lattice_ast         := Ast_distributive_lattice_and_or
|}.



End CAS.

Section Verify.

Theorem correct_distributive_lattice_and_or :
      distributive_lattice_and_or = A2C_distributive_lattice bool (A_distributive_lattice_and_or). 
Proof. compute. reflexivity. Qed. 

 
End Verify.   
  