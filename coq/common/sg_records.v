Require Import CAS.coq.common.compute. 
Require Import CAS.coq.common.eqv_records. 
Require Import CAS.coq.common.sg_certificates.
Require Import CAS.coq.common.sg_cert_records. 
Require Import CAS.coq.common.ast.


Record sg {S : Type} := {
  sg_eq           : @eqv S 
; sg_bop          : binary_op S
; sg_exists_id_d  : @check_exists_id S
; sg_exists_ann_d : @check_exists_ann S
; sg_certs        : @sg_certificates S
; sg_ast          : cas_ast
}.


Record sg_C {S : Type} := {
  sg_C_eqv          : @eqv S 
; sg_C_bop          : binary_op S
; sg_C_exists_id_d  : @check_exists_id S
; sg_C_exists_ann_d : @check_exists_ann S
; sg_C_certs        : @sg_C_certificates S
; sg_C_ast          : cas_ast
}.

Record sg_CI {S : Type} := {
  sg_CI_eqv          : @eqv S 
; sg_CI_bop          : binary_op S
; sg_CI_exists_id_d  : @check_exists_id S
; sg_CI_exists_ann_d : @check_exists_ann S
; sg_CI_certs        : @sg_CI_certificates S
; sg_CI_ast          : cas_ast
}.

Record sg_CI_with_ann {S : Type} := {
  sg_CI_wa_eqv          : @eqv S 
; sg_CI_wa_bop          : binary_op S
; sg_CI_wa_exists_id_d  : @check_exists_id S
; sg_CI_wa_exists_ann   : @assert_exists_ann S
; sg_CI_wa_certs        : @sg_CI_certificates S
; sg_CI_wa_ast          : cas_ast
}.



Record sg_CS {S : Type} := {
  sg_CS_eqv          : @eqv S 
; sg_CS_bop          : binary_op S
; sg_CS_exists_id_d  : @check_exists_id S
; sg_CS_exists_ann_d : @check_exists_ann S
; sg_CS_certs        : @sg_CS_certificates S
; sg_CS_ast          : cas_ast
}.

Record sg_CK {S : Type} := {
  sg_CK_eqv         : @eqv S
; sg_CK_bop         : binary_op S
; sg_CK_exists_id_d : @check_exists_id S
; sg_CK_certs       : @sg_CK_certificates S
; sg_CK_ast         : cas_ast
}.

Record asg {S : Type} := {
  asg_eq           : @eqv S 
; asg_bop          : binary_op S
; asg_exists_id_d  : @check_exists_id S
; asg_exists_ann_d : @check_exists_ann S
; asg_certs        : @asg_certificates S
; asg_ast          : cas_ast
}.

Record msg {S : Type} := {
  msg_eq           : @eqv S 
; msg_bop          : binary_op S
; msg_exists_id_d  : @check_exists_id S
; msg_exists_ann_d : @check_exists_ann S
; msg_certs        : @msg_certificates S
; msg_ast          : cas_ast
}.

