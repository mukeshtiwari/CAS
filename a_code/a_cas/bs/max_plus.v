Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.

Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.a_code.proof_records.
Require Import CAS.a_code.a_cas_records.

Require Import CAS.a_code.a_cas.eqv.nat.
Require Import CAS.a_code.a_cas.sg.max.
Require Import CAS.a_code.a_cas.sg.plus.

Require Import CAS.theory.bs.max_plus.

Definition semiring_proofs_max_plus : semiring_proofs nat brel_eq_nat bop_max bop_plus := 
  {| 
     A_semiring_left_distributive      := bop_max_plus_left_distributive
   ; A_semiring_right_distributive     := bop_max_plus_right_distributive

   ; A_semiring_plus_id_is_times_ann_d   := inr _ bop_max_plus_not_id_equals_ann
   ; A_semiring_times_id_is_plus_ann_d   := inr _ bop_plus_max_not_id_equals_ann

   ; A_semiring_left_left_absorptive_d   := inr _ bops_max_plus_not_left_left_absorptive
   ; A_semiring_left_right_absorptive_d  := inr _ bops_max_plus_not_left_right_absorptive
  |}. 

Definition A_dioid_max_plus : A_dioid nat := 
{|
  A_dioid_eqv          := A_eqv_nat 
; A_dioid_plus         := bop_max
; A_dioid_times        := bop_plus
; A_dioid_plus_proofs  := A_sg_CI_proofs _ A_sg_CI_max
; A_dioid_times_proofs := A_sg_proofs _ A_sg_plus
; A_dioid_proofs       := semiring_proofs_max_plus
; A_dioid_ast          := Ast_dioid_max_plus
|}.

