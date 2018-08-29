Require Import CAS.coq.common.base. 
Require Import CAS.coq.eqv.nat.
Require Import CAS.coq.sg.max.
Require Import CAS.coq.sg.min.
Require Import CAS.coq.sg.cast_up.
Require Import CAS.coq.theory.facts. 

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


End Theory.

Section ACAS.

Definition distributive_lattice_proofs_min_max : distributive_lattice_proofs nat  brel_eq_nat bop_min bop_max := 
  {|
     A_distributive_lattice_absorptive        := bops_min_max_left_left_absorptive
   ; A_distributive_lattice_absorptive_dual   := bops_max_min_left_left_absorptive                                                 
   ; A_distributive_lattice_distributive      := bops_min_max_left_distributive
  |}. 

Definition A_selective_distributive_lattice_min_max : A_selective_distributive_lattice nat := 
{|
  A_selective_distributive_lattice_eqv          := A_eqv_nat
; A_selective_distributive_lattice_join         := bop_min
; A_selective_distributive_lattice_meet         := bop_max
; A_selective_distributive_lattice_join_proofs  := A_sg_CS_proofs _ A_sg_CS_min
; A_selective_distributive_lattice_meet_proofs  := A_sg_CS_proofs _ A_sg_CS_max
; A_selective_distributive_lattice_proofs       := distributive_lattice_proofs_min_max
; A_selective_distributive_lattice_join_ast     := Ast_bop_min
; A_selective_distributive_lattice_meet_ast    := Ast_bop_max
; A_selective_distributive_lattice_ast          := Ast_selective_distributive_lattice_min_max
|}.

End ACAS.

Section CAS.


Definition distributive_lattice_certs_min_max : @distributive_lattice_certificates nat := 
  {| 
     distributive_lattice_distributive      := Assert_Left_Distributive 
   ; distributive_lattice_absorptive_dual   := Assert_Left_Left_Absorptive_Dual
   ; distributive_lattice_absorptive        := Assert_Left_Left_Absorptive
  |}. 



Definition selective_distributive_lattice_min_max : @selective_distributive_lattice nat := 
{|
  selective_distributive_lattice_eqv          := eqv_eq_nat 
; selective_distributive_lattice_join         := bop_min
; selective_distributive_lattice_meet        := bop_max
; selective_distributive_lattice_join_certs  := sg_CS_certs sg_CS_min
; selective_distributive_lattice_meet_certs  := sg_CS_certs sg_CS_max
; selective_distributive_lattice_certs       := distributive_lattice_certs_min_max
; selective_distributive_lattice_join_ast    := Ast_bop_min
; selective_distributive_lattice_meet_ast    := Ast_bop_max                                                  
; selective_distributive_lattice_ast         := Ast_selective_distributive_lattice_min_max
|}.

End CAS.

Section Verify.

Theorem correct_selective_distributive_lattice_min_max : 
   selective_distributive_lattice_min_max = A2C_selective_distributive_lattice nat (A_selective_distributive_lattice_min_max). 
Proof. compute. reflexivity. Qed. 
  
 
End Verify.   
  