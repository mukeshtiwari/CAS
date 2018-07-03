Require Import CAS.code.basic_types. 
Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records. 
Require Import CAS.code.ast.
Require Import CAS.code.data.

(* eqv *) 
Record eqv {S : Type} := {
  eqv_eq    : brel S 

; eqv_witness : S         
; eqv_new     : S -> S                                                                                                   

; eqv_data  : S -> data (* for printing in ocaml-land *) 
; eqv_rep   : S -> S    (* for reductions.  Should this be an option? *) 
; eqv_ast   : ast_eqv
}.  

(* orders *) 

(* quasi order 
Record qo {S : Type} := {
  qo_eqv        : eqv S 
; qo_brel       : brel S 
; qo_certs      : qo_certificates S
; qo_ast        : ast_qo
}.
*) 

(* partial order *) 
Record po {S : Type} := {
  po_eqv        : eqv (S := S)  
; po_brel       : brel S 
; po_certs      : po_certificates (S := S) 
; po_ast        : ast_po
}.

(* total order *) 
Record to {S : Type} := {
  to_eqv        : eqv (S := S)  
; to_brel       : brel S 
; to_certs      : to_certificates (S := S)  
; to_ast        : ast_to
}.
