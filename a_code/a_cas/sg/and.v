Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cas.sg.cast_up. 

Require Import CAS.a_code.a_cas.eqv.bool.
Require Import CAS.theory.bop.and.

Require Import CAS.theory.facts. 

Definition sg_CS_proofs_and : sg_CS_proofs bool brel_eq_bool bop_and := 
{| 
  A_sg_CS_associative  := bop_and_associative
; A_sg_CS_congruence   := bop_and_congruence
; A_sg_CS_commutative  := bop_and_commutative
; A_sg_CS_selective    := bop_and_selective
; A_sg_CS_exists_id_d  := inl _ bop_and_exists_id 
; A_sg_CS_exists_ann_d := inl _ bop_and_exists_ann 
|}. 

Definition A_sg_CS_and : A_sg_CS bool
:= {| 
     A_sg_CS_eqv         := A_eqv_bool
   ; A_sg_CS_bop         := bop_and
   ; A_sg_CS_proofs      := sg_CS_proofs_and
   ; A_sg_CS_ast         := Ast_sg_CS_and 
   |}. 

Definition A_sg_and : A_sg bool := A_sg_from_sg_CS bool A_sg_CS_and.

Definition A_sg_CI_and : A_sg_CI bool := A_sg_CI_from_sg_CS bool A_sg_CS_and. 