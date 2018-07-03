Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.brel.eq_nat. 
Require Import CAS.theory.bop.times.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cas.eqv.nat. 
Require Import CAS.theory.facts.


Definition sg_C_proofs_times : sg_C_proofs nat brel_eq_nat bop_times := 
{| 
  A_sg_C_associative      := bop_times_associative
; A_sg_C_congruence       := bop_times_congruence
; A_sg_C_commutative      := bop_times_commutative
; A_sg_C_selective_d      := inr _ bop_times_not_selective
; A_sg_C_idempotent_d     := inr _ bop_times_not_idempotent 
; A_sg_C_exists_id_d      := inl _ bop_times_exists_id
; A_sg_C_exists_ann_d     := inl _ bop_times_exists_ann
; A_sg_C_left_cancel_d    := inr _ bop_times_not_left_cancellative
; A_sg_C_right_cancel_d   := inr _ bop_times_not_right_cancellative
; A_sg_C_left_constant_d  := inr _ bop_times_not_left_constant
; A_sg_C_right_constant_d := inr _ bop_times_not_right_constant
; A_sg_C_anti_left_d      := inr _ bop_times_not_anti_left
; A_sg_C_anti_right_d     := inr _ bop_times_not_anti_right
|}. 



Definition A_sg_C_times : A_sg_C nat 
:= {| 
     A_sg_C_eqv         := A_eqv_nat 
   ; A_sg_C_bop        := bop_times
   ; A_sg_C_proofs     := sg_C_proofs_times 
   ; A_sg_C_ast        := Ast_sg_C_times
   |}. 

