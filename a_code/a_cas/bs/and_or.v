Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.brel.eq_bool. 
Require Import CAS.theory.bop.or.
Require Import CAS.theory.bop.and.
Require Import CAS.theory.bs.and_or.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cas.eqv.bool.
Require Import CAS.a_code.a_cas.sg.or.
Require Import CAS.a_code.a_cas.sg.and. 

Definition bs_proofs_and_or : bs_proofs bool  brel_eq_bool bop_and bop_or := 
  {| 
     A_bs_left_distributive_d      := inl _ bops_and_or_left_distributive
   ; A_bs_right_distributive_d     := inl _ bops_and_or_right_distributive
   ; A_bs_plus_id_is_times_ann_d   := inl _ bops_and_or_id_equals_ann
   ; A_bs_times_id_is_plus_ann_d   := inl _ bops_and_or_ann_equals_id 
   ; A_bs_left_left_absorptive_d   := inl _ bops_and_or_left_left_absorptive
   ; A_bs_left_right_absorptive_d  := inl _ bops_and_or_left_right_absorptive
   ; A_bs_right_left_absorptive_d  := inl _ bops_and_or_right_left_absorptive
   ; A_bs_right_right_absorptive_d := inl _ bops_and_or_right_right_absorptive
  |}. 


Definition A_bs_and_or : A_bs bool := 
{|
  A_bs_eqv          := A_eqv_bool
; A_bs_plus         := bop_and
; A_bs_times        := bop_or
; A_bs_plus_proofs  := sg_proofs_and
; A_bs_times_proofs := sg_proofs_or
; A_bs_proofs       := bs_proofs_and_or 
; A_bs_ast          := Ast_bs_and_or
|}.

