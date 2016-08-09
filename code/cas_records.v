Require Import CAS.code.basic_types. 
Require Import CAS.code.certificates.
Require Import CAS.code.cert_records. 
Require Import CAS.code.ast.
Require Import CAS.code.data.


(* eqv *) 
Record eqv (S : Type) := {
  eqv_eq    : brel S 
  (* should eqv have a canonical : S -> S function *) 
; eqv_certs : eqv_certificates S
; eqv_data  : S -> data (* for printing in ocaml-land *) 
; eqv_rep   : S -> S    (* for reductions.  Should this be an option? *) 
; eqv_ast   : ast_eqv
}.  


(* orders *) 

(* quasi order 
Record qo (S : Type) := {
  qo_eqv        : eqv S 
; qo_brel       : brel S 
; qo_certs      : qo_certificates S
; qo_ast        : ast_qo
}.
*) 

(* partial order *) 
Record po (S : Type) := {
  po_eqv        : eqv S 
; po_brel       : brel S 
; po_certs      : po_certificates S
; po_ast        : ast_po
}.

(* total order *) 
Record to (S : Type) := {
  to_eqv        : eqv S 
; to_brel       : brel S 
; to_certs      : to_certificates S 
; to_ast        : ast_to
}.


(* semigroups *) 
Record sg (S : Type) := {
  sg_eq    : eqv S 
; sg_bop   : binary_op S 
; sg_certs : sg_certificates S 
; sg_ast   : ast_sg
}.

(*
Record sg_new (S : Type) := {
  sgn_eq    : eqv S 
; sgn_bop   : binary_op S 
; sgn_certs : sg_certificates_new S 
; sgn_ast   : ast_sg
}.
*) 

Record sg_C (S : Type) := {
  sg_C_eqv   : eqv S 
; sg_C_bop   : binary_op S 
; sg_C_certs : sg_C_certificates S 
; sg_C_ast   : ast_sg_C
}.


Record sg_CI (S : Type) := {
  sg_CI_eqv   : eqv S 
; sg_CI_bop   : binary_op S 
; sg_CI_certs : sg_CI_certificates S 
; sg_CI_ast   : ast_sg_CI
}.

Record sg_CS (S : Type) := {
  sg_CS_eqv   : eqv S 
; sg_CS_bop   : binary_op S 
; sg_CS_certs : sg_CS_certificates S
; sg_CS_ast   : ast_sg_CS
}.


Record sg_CK (S : Type) := {
  sg_CK_eqv   : eqv S 
; sg_CK_bop   : binary_op S 
; sg_CK_certs : sg_CK_certificates S
; sg_CK_ast   : ast_sg_CK
}.


Record bs (S : Type) := {
  bs_eqv         : eqv S 
; bs_plus        : binary_op S 
; bs_times       : binary_op S 
; bs_plus_certs  : sg_certificates S 
; bs_times_certs : sg_certificates S 
; bs_certs       : bs_certificates S 
; bs_ast         : ast_bs
}.

Record bs_CS (S : Type) := {
  bs_CS_eqv         : eqv S 
; bs_CS_plus        : binary_op S 
; bs_CS_times       : binary_op S 
; bs_CS_plus_certs  : sg_CS_certificates S 
; bs_CS_times_certs : sg_certificates S    
; bs_CS_certs       : bs_certificates S 
; bs_CS_ast         : ast_bs_CS
}.


Record bs_C (S : Type) := {
  bs_C_eqv         : eqv S 
; bs_C_plus        : binary_op S 
; bs_C_times       : binary_op S 
; bs_C_plus_certs  : sg_C_certificates S 
; bs_C_times_certs : sg_certificates S    
; bs_C_certs       : bs_certificates S 
; bs_C_ast         : ast_bs_C
}.



