Require Import CAS.coq.common.compute. 
Require Import CAS.coq.common.eqv_certificates.
Require Import CAS.coq.common.ast.


Set Implicit Arguments.
Unset Strict Implicit.

(* equiv relations *) 
Record eqv_certificates {S : Type} := 
{
  eqv_congruence     : @assert_brel_congruence S 
; eqv_reflexive      : @assert_reflexive S 
; eqv_transitive     : @assert_transitive S 
; eqv_symmetric      : @assert_symmetric S
; eqv_type_ast       : ast_type                                                                                                                         
; eqv_brel_ast       : ast_brel
}.


(* orders *) 

(* quasi-order *) 
Record qo_certificates {S : Type}  := {
  qo_congruence      : @assert_brel_congruence S 
; qo_reflexive       : @assert_reflexive S 
; qo_transitive      : @assert_transitive S
; qo_antisymmetric_d : @check_antisymmetric S 
; qo_total_d         : @check_total S 
; qo_brel_ast        : ast_brel
}.

(* partial-order *) 
Record po_certificates {S : Type} := {
  po_congruence       : @assert_brel_congruence S 
; po_reflexive        : @assert_reflexive S 
; po_transitive       : @assert_transitive S
; po_antisymmetric    : @assert_antisymmetric S 
; po_total_d          : @check_total S
; po_exists_top_d     : @check_exists_top S 
; po_exists_bottom_d  : @check_exists_bottom S 
; po_bottoms_finite_d : @check_bottoms_finite S
; po_brel_ast         : ast_brel       
}.

(* total-order *) 
Record to_certificates {S : Type} := {
  to_congruence    : @assert_brel_congruence S 
; to_reflexive     : @assert_reflexive S 
; to_transitive    : @assert_transitive S
; to_antisymmetric : @assert_antisymmetric S 
; to_total         : @assert_total S 
; to_brel_ast      : ast_brel
}.



