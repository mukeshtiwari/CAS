Require Import CAS.coq.common.compute. 
Require Import CAS.coq.common.eqv_certificates.
Require Import CAS.coq.common.eqv_cert_records. 
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.

(* eqv *) 
Record eqv {S : Type} := {
  eqv_eq            : brel S
; eqv_certs         : @eqv_certificates S                                                   
; eqv_witness       : S         
; eqv_new           : S -> S                                                                                                   
; eqv_exactly_two_d : @check_exactly_two S 
; eqv_data          : S -> data (* for printing in ocaml-land *) 
; eqv_rep           : S -> S    (* for reductions.  Should this be an option? *)
; eqv_finite_d      : @check_is_finite S 
; eqv_ast           : cas_ast
}.  

(* orders *) 

(* quasi order *)
Record qo {S : Type} := {
  qo_eqv        : @eqv S 
; qo_brel       : @brel S 
; qo_certs      : @qo_certificates S
; qo_ast        : cas_ast
}.


(* partial order *) 
Record po {S : Type} := {
  po_eqv             : @eqv S
; po_lte             : @brel S
; po_exists_top_d    : @check_exists_top S 
; po_exists_bottom_d : @check_exists_bottom S 
; po_certs           : @po_certificates S
; po_ast             : cas_ast
}.

Record po_with_bottom {S : Type} := {
  powb_eqv             : @eqv S
; powb_lte             : @brel S
; powb_exists_top_d    : @check_exists_top S 
; powb_exists_bottom   : @assert_exists_bottom S 
; powb_certs           : @po_certificates S
; powb_ast             : cas_ast
}.

(* total order *) 
Record to {S : Type} := {
  to_eqv        : @eqv S
; to_brel       : @brel S 
; to_certs      : @to_certificates S
; to_ast        : cas_ast
}.
