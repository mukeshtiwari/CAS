Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cas.sg.cast_up.

Require Import CAS.a_code.a_cas.eqv.nat.
Require Import CAS.theory.bop.min.


Definition sg_CS_proofs_min : sg_CS_proofs nat brel_eq_nat bop_min := 
{| 
  A_sg_CS_associative  := bop_min_associative
; A_sg_CS_congruence   := bop_min_congruence
; A_sg_CS_commutative  := bop_min_commutative
; A_sg_CS_selective    := bop_min_selective
; A_sg_CS_exists_id_d  := inr _ bop_min_not_exists_id
; A_sg_CS_exists_ann_d := inl _ bop_min_exists_ann
|}. 



Definition A_sg_CS_min : A_sg_CS nat 
:= {| 
     A_sg_CS_eqv         := A_eqv_nat 
   ; A_sg_CS_bop         := bop_min 
   ; A_sg_CS_proofs      := sg_CS_proofs_min 
   ; A_sg_CS_ast         := Ast_sg_CS_min 
   |}. 


Definition A_sg_min : A_sg nat := A_sg_from_sg_CS nat A_sg_CS_min.

Definition A_sg_CI_min : A_sg_CI nat := A_sg_CI_from_sg_CS nat A_sg_CS_min.

Definition A_sg_C_min : A_sg_C nat := A_sg_C_from_sg_CS nat A_sg_CS_min. 