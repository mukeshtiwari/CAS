Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cas.sg.cast_up.

Require Import CAS.a_code.a_cas.eqv.nat.
Require Import CAS.theory.bop.plus.


Definition sg_CK_proofs_plus : sg_CK_proofs nat brel_eq_nat bop_plus := 
{| 
  A_sg_CK_associative        := bop_plus_associative
; A_sg_CK_congruence         := bop_plus_congruence
; A_sg_CK_commutative        := bop_plus_commutative
; A_sg_CK_left_cancel        := bop_plus_left_cancellative 
; A_sg_CK_exists_id_d        := inl _ bop_plus_exists_id 
; A_sg_CK_anti_left_d        := inr _ bop_plus_not_anti_left
; A_sg_CK_anti_right_d       := inr _ bop_plus_not_anti_right
|}. 



Definition A_sg_CK_plus : A_sg_CK nat 
:= {| 
     A_sg_CK_eqv         := A_eqv_nat 
   ; A_sg_CK_bop         := bop_plus
   ; A_sg_CK_proofs      := sg_CK_proofs_plus
   ; A_sg_CK_ast         := Ast_sg_CK_plus 
   |}. 


Definition A_sg_plus : A_sg nat := A_sg_from_sg_CK nat A_sg_CK_plus. 