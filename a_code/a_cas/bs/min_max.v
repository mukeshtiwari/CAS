Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.

Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.a_code.proof_records.
Require Import CAS.a_code.a_cas_records.

Require Import CAS.a_code.a_cas.eqv.nat.
Require Import CAS.a_code.a_cas.sg.max.
Require Import CAS.a_code.a_cas.sg.min.
Require Import CAS.a_code.a_cas.bs.dual.

Require Import CAS.theory.bs.min_max.
Require Import CAS.theory.bs.max_min.

Definition distributive_lattice_proofs_min_max : distributive_lattice_proofs nat  brel_eq_nat bop_min bop_max := 
  {|
     A_distributive_lattice_absorptive        := bops_min_max_left_left_absorptive
   ; A_distributive_lattice_absorptive_dual   := bops_max_min_left_left_absorptive                                                 
   ; A_distributive_lattice_distributive      := bops_min_max_left_distributive
(*                                                   
   ; A_distributive_lattice_distributive_dual := bops_max_min_left_distributive                                                 
*)
  |}. 

Definition A_distributive_lattice_min_max : A_distributive_lattice nat := 
{|
  A_distributive_lattice_eqv          := A_eqv_nat
; A_distributive_lattice_join         := bop_min
; A_distributive_lattice_meet         := bop_max
; A_distributive_lattice_join_proofs  := A_sg_CI_proofs _ (A_sg_CI_min)
; A_distributive_lattice_meet_proofs  := A_sg_CI_proofs _ (A_sg_CI_max)
; A_distributive_lattice_proofs       := distributive_lattice_proofs_min_max
; A_distributive_lattice_ast          := Ast_distributive_lattice_min_max
|}.

