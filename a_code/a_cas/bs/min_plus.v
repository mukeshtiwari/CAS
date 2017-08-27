Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.

Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.a_code.proof_records.
Require Import CAS.a_code.a_cas_records.

Require Import CAS.a_code.a_cas.eqv.nat.
Require Import CAS.a_code.a_cas.sg.min.
Require Import CAS.a_code.a_cas.sg.plus.

Require Import CAS.theory.bs.min_plus.


Definition semiring_proofs_min_plus : semiring_proofs nat brel_eq_nat bop_min bop_plus := 
  {| 
     A_semiring_left_distributive      := bop_min_plus_left_distributive
   ; A_semiring_right_distributive     := bop_min_plus_right_distributive

   ; A_semiring_plus_id_is_times_ann_d   := inr _ bop_min_plus_not_id_equals_ann
   ; A_semiring_times_id_is_plus_ann_d   := inl _ bop_min_plus_ann_equals_id 

   ; A_semiring_left_left_absorptive_d   := inl _ bops_min_plus_left_left_absorptive
   ; A_semiring_left_right_absorptive_d  := inl _ bops_min_plus_left_right_absorptive
  |}. 

Definition A_dioid_min_plus : A_dioid nat := 
{|
  A_dioid_eqv          := A_eqv_nat 
; A_dioid_plus         := bop_min
; A_dioid_times        := bop_plus
; A_dioid_plus_proofs  := A_sg_CI_proofs _ A_sg_CI_min
; A_dioid_times_proofs := A_sg_proofs _ A_sg_plus
; A_dioid_proofs       := semiring_proofs_min_plus
; A_dioid_ast          := Ast_dioid_min_plus
|}.

