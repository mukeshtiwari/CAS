Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.

Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.a_code.proof_records.
Require Import CAS.a_code.a_cas_records.

Require Import CAS.a_code.a_cas.eqv.bool.
Require Import CAS.a_code.a_cas.sg.or.
Require Import CAS.a_code.a_cas.sg.and.
Require Import CAS.a_code.a_cas.bs.dual.

Require Import CAS.theory.bs.and_or.
Require Import CAS.theory.bs.or_and.

Definition distributive_lattice_proofs_and_or : distributive_lattice_proofs bool  brel_eq_bool bop_and bop_or := 
  {|
     A_distributive_lattice_absorptive        := bops_and_or_left_left_absorptive
   ; A_distributive_lattice_absorptive_dual   := bops_or_and_left_left_absorptive                                                 
   ; A_distributive_lattice_distributive      := bops_and_or_left_distributive
(*                                                   
   ; A_distributive_lattice_distributive_dual := bops_or_and_left_distributive 
*)                                                
  |}. 

Definition A_distributive_lattice_and_or : A_distributive_lattice bool := 
{|
  A_distributive_lattice_eqv          := A_eqv_bool
; A_distributive_lattice_join         := bop_and
; A_distributive_lattice_meet         := bop_or
; A_distributive_lattice_join_proofs  := A_sg_CI_proofs _ (A_sg_CI_and)
; A_distributive_lattice_meet_proofs  := A_sg_CI_proofs _ (A_sg_CI_or)
; A_distributive_lattice_proofs       := distributive_lattice_proofs_and_or
; A_distributive_lattice_ast          := Ast_distributive_lattice_and_or
|}.

