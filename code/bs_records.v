Require Import CAS.code.basic_types. 
Require Import CAS.code.eqv_records. 
Require Import CAS.code.sg_cert_records. 
Require Import CAS.code.bs_cert_records. 
Require Import CAS.code.ast.


Record bs {S : Type} := {
  bs_eqv         : eqv (S := S) 
; bs_plus        : binary_op S 
; bs_times       : binary_op S 
; bs_plus_certs  : sg_certificates (S := S) 
; bs_times_certs : sg_certificates (S := S) 
; bs_certs       : bs_certificates (S := S) 
; bs_ast         : ast_bs
}.


Record bs_CS {S : Type} := {
  bs_CS_eqv         : eqv (S := S) 
; bs_CS_plus        : binary_op S 
; bs_CS_times       : binary_op S 
; bs_CS_plus_certs  : sg_CS_certificates (S := S) 
; bs_CS_times_certs : sg_certificates (S := S)    
; bs_CS_certs       : bs_certificates (S := S) 
; bs_CS_ast         : ast_bs_CS
}.

Record bs_C {S : Type} := {
  bs_C_eqv         : @eqv S  
; bs_C_plus        : binary_op S 
; bs_C_times       : binary_op S 
; bs_C_plus_certs  : @sg_C_certificates S 
; bs_C_times_certs : @sg_certificates S
; bs_C_certs       : @bs_certificates S 
; bs_C_ast         : ast_bs_C
}.

Record semiring {S : Type} := {
  semiring_eqv         : @eqv S 
; semiring_plus        : binary_op S 
; semiring_times       : binary_op S 
; semiring_plus_certs  : @sg_C_certificates S 
; semiring_times_certs : @sg_certificates S   
; semiring_certs       : @semiring_certificates S 
; semiring_ast         : ast_semiring
}.

Record dioid {S : Type} := {
  dioid_eqv         : @eqv S 
; dioid_plus        : binary_op S 
; dioid_times       : binary_op S 
; dioid_plus_certs  : @sg_CI_certificates S 
; dioid_times_certs : @sg_certificates S   
; dioid_certs       : @semiring_certificates S 
; dioid_ast         : ast_dioid
}.

Record lattice {S : Type} := {
  lattice_eqv         : @eqv S 
; lattice_join        : binary_op S 
; lattice_meet        : binary_op S 
; lattice_join_certs : @sg_CI_certificates S 
; lattice_meet_certs : @sg_CI_certificates S 
; lattice_certs      : @lattice_certificates S 
; lattice_ast         : ast_lattice
}.


Record distributive_lattice {S : Type} := {
  distributive_lattice_eqv        : @eqv S 
; distributive_lattice_join       : binary_op S 
; distributive_lattice_meet       : binary_op S 
; distributive_lattice_join_certs : @sg_CI_certificates S 
; distributive_lattice_meet_certs : @sg_CI_certificates S 
; distributive_lattice_certs      : @distributive_lattice_certificates S
; distributive_lattice_ast        : ast_distributive_lattice
}.

