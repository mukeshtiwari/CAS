Require Import CAS.code.basic_types. 
Require Import CAS.code.eqv_certificates.


Set Implicit Arguments.
Unset Strict Implicit.

(* eqv 

Record eqv_certificates {S : Type} := {
  eqv_nontrivial    : assert_nontrivial (S := S)          
; eqv_congruence    : assert_brel_congruence (S := S) 
; eqv_reflexive     : assert_reflexive (S := S) 
; eqv_symmetric     : assert_symmetric (S := S) 
; eqv_transitive    : assert_transitive (S := S)
}.
*) 

(* orders *) 

(* quasi-order *) 
Record qo_certificates {S : Type}  := {
  qo_congruence      : assert_brel_congruence (S := S) 
; qo_reflexive       : assert_reflexive (S := S) 
; qo_transitive      : assert_transitive (S := S)
; qo_antisymmetric_d : check_antisymmetric (S := S) 
; qo_total_d         : check_total (S := S) 
}.

(* partial-order *) 
Record po_certificates {S : Type} := {
  po_congruence    : assert_brel_congruence (S := S) 
; po_reflexive     : assert_reflexive (S := S) 
; po_transitive    : assert_transitive (S := S)
; po_antisymmetric : assert_antisymmetric (S := S) 
; po_total_d       : check_total (S := S) 
}.

(* total-order *) 
Record to_certificates {S : Type} := {
  to_congruence    : assert_brel_congruence (S := S) 
; to_reflexive     : assert_reflexive (S := S) 
; to_transitive    : assert_transitive (S := S)
; to_antisymmetric : assert_antisymmetric (S := S) 
; to_total         : assert_total (S := S) 
}.



