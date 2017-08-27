Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.brel.eq_nat. 
Require Import CAS.theory.bop.plus.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cas.brel.eqv_nat. 
Require Import CAS.theory.facts. 


Definition A_sg_plus : A_sg nat 
:= {| 
     A_sg_eq          := A_eqv_nat 
   ; A_sg_bop         := bop_plus
   ; A_sg_proofs      := sg_proofs_plus
   ; A_sg_ast         := Ast_sg_plus 
   |}. 
