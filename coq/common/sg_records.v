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

Record asg {S : Type} := {
  asg_eq      : eqv (S := S) 
; asg_bop     : binary_op S 
; asg_certs   : asg_certificates (S := S)
; asg_bop_ast : ast_bop                      
; asg_ast     : ast_asg
}.

Record msg {S : Type} := {
  msg_eq      : eqv (S := S) 
; msg_bop     : binary_op S 
; msg_certs   : msg_certificates (S := S)
; msg_bop_ast : ast_bop                      
; msg_ast     : ast_msg
}.



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
; sg_CS_bop_ast  : ast_bop
; sg_CS_ast   : ast_sg_CS
}.

Record sg_CK {S : Type} := {
  sg_CK_eqv   : eqv (S := S) 
; sg_CK_bop   : binary_op S 
; sg_CK_certs : sg_CK_certificates (S := S)
; sg_CK_bop_ast     : ast_bop   
; sg_CK_ast   : ast_sg_CK
}.

