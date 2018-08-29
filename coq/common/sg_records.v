Require Import CAS.coq.common.compute. 
Require Import CAS.coq.common.eqv_records. 
Require Import CAS.coq.common.sg_certificates.
Require Import CAS.coq.common.sg_cert_records. 
Require Import CAS.coq.common.ast.


Record sg {S : Type} := {
  sg_eq      : eqv (S := S) 
; sg_bop     : binary_op S 
; sg_certs   : sg_certificates (S := S)
; sg_bop_ast : ast_bop                      
; sg_ast     : ast_sg
}.

(*
Record sg_new {S : Type} := {
  sgn_eq    : eqv S 
; sgn_bop   : binary_op S 
; sgn_certs : sg_certificates_new S 
; sgn_ast   : ast_sg
}.
*) 

Record sg_C {S : Type} := {
  sg_C_eqv   : eqv (S := S) 
; sg_C_bop   : binary_op S 
; sg_C_certs : sg_C_certificates (S := S)
; sg_C_bop_ast     : ast_bop                      
; sg_C_ast   : ast_sg_C
}.

Record sg_CI {S : Type} := {
  sg_CI_eqv   : eqv (S := S) 
; sg_CI_bop   : binary_op S 
; sg_CI_certs : sg_CI_certificates (S := S)
; sg_CI_bop_ast      : ast_bop                                                            
; sg_CI_ast   : ast_sg_CI
}.

Record sg_CS {S : Type} := {
  sg_CS_eqv   : eqv (S := S) 
; sg_CS_bop   : binary_op S 
; sg_CS_certs : sg_CS_certificates (S := S)
; sg_CS_bop_ast      : ast_bop
; sg_CS_ast   : ast_sg_CS
}.

Record sg_CK {S : Type} := {
  sg_CK_eqv   : eqv (S := S) 
; sg_CK_bop   : binary_op S 
; sg_CK_certs : sg_CK_certificates (S := S)
; sg_CK_bop_ast     : ast_bop                                                           
; sg_CK_ast   : ast_sg_CK
}.

