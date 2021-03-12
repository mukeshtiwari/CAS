Require Import CAS.coq.common.compute. 
Require Import CAS.coq.common.eqv_records. 
Require Import CAS.coq.common.sg_cert_records. 
Require Import CAS.coq.common.bs_cert_records. 
Require Import CAS.coq.common.ast.


Record bs {S : Type} := {
  bs_eqv           : eqv (S := S) 
; bs_plus          : binary_op S 
; bs_times         : binary_op S 
; bs_plus_certs    : asg_certificates (S := S) 
; bs_times_certs   : msg_certificates (S := S)
; bs_id_ann_certs  : id_ann_certificates (S := S)
; bs_certs         : bs_certificates (S := S)
; bs_ast           : ast_bs
}.


Record bs_CS {S : Type} := {
  bs_CS_eqv          : eqv (S := S) 
; bs_CS_plus         : binary_op S 
; bs_CS_times        : binary_op S 
; bs_CS_plus_certs   : sg_CS_certificates (S := S) 
; bs_CS_times_certs  : msg_certificates (S := S)
; bs_CS_id_ann_certs : id_ann_certificates (S := S) 
; bs_CS_certs        : bs_certificates (S := S)
; bs_CS_ast          : ast_bs_CS
}.

Record bs_CI {S : Type} := {
  bs_CI_eqv          : eqv (S := S) 
; bs_CI_plus         : binary_op S 
; bs_CI_times        : binary_op S 
; bs_CI_plus_certs   : sg_CI_certificates (S := S) 
; bs_CI_times_certs  : msg_certificates (S := S)
; bs_CI_id_ann_certs : id_ann_certificates (S := S)               
; bs_CI_certs        : bs_certificates (S := S)
; bs_CI_ast          : ast_bs_CI
}.


Record presemiring {S : Type} := {
  presemiring_eqv          : @eqv S 
; presemiring_plus         : binary_op S 
; presemiring_times        : binary_op S 
; presemiring_plus_certs   : @sg_C_certificates S 
; presemiring_times_certs  : @msg_certificates S
; presemiring_id_ann_certs : @id_ann_certificates S
; presemiring_certs        : @semiring_certificates S
; presemiring_ast          : ast_presemiring
}.

Record selective_presemiring {S : Type} := {
  selective_presemiring_eqv          : @eqv S 
; selective_presemiring_plus         : binary_op S 
; selective_presemiring_times        : binary_op S 
; selective_presemiring_plus_certs   : @sg_CS_certificates S 
; selective_presemiring_times_certs  : @msg_certificates S
; selective_presemiring_id_ann_certs : @id_ann_certificates S
; selective_presemiring_certs        : @semiring_certificates S
; selective_presemiring_ast          : ast_selective_presemiring
}.



Record semiring {S : Type} := {
  semiring_eqv          : @eqv S 
; semiring_plus         : binary_op S 
; semiring_times        : binary_op S 
; semiring_plus_certs   : @sg_C_certificates S 
; semiring_times_certs  : @msg_certificates S
; semiring_id_ann_certs : @zero_one_certificates S
; semiring_certs        : @semiring_certificates S
; semiring_ast          : ast_semiring
}.


Record selective_semiring {S : Type} := {
  selective_semiring_eqv          : @eqv S 
; selective_semiring_plus         : binary_op S 
; selective_semiring_times        : binary_op S 
; selective_semiring_plus_certs   : @sg_CS_certificates S 
; selective_semiring_times_certs  : @msg_certificates S
; selective_semiring_id_ann_certs : @zero_one_certificates S
; selective_semiring_certs        : @semiring_certificates S
; selective_semiring_ast          : ast_selective_semiring
}.

Record dioid {S : Type} := {
  dioid_eqv          : @eqv S 
; dioid_plus         : binary_op S 
; dioid_times        : binary_op S 
; dioid_plus_certs   : @sg_CI_certificates S 
; dioid_times_certs  : @msg_certificates S
; dioid_id_ann_certs : @bounded_certificates S
; dioid_certs        : @semiring_certificates S
; dioid_ast          : ast_dioid
}.

Record selective_dioid {S : Type} := {
  selective_dioid_eqv          : @eqv S 
; selective_dioid_plus         : binary_op S 
; selective_dioid_times        : binary_op S 
; selective_dioid_plus_certs   : @sg_CS_certificates S 
; selective_dioid_times_certs  : @msg_certificates S
; selective_dioid_id_ann_certs : @bounded_certificates S                  
; selective_dioid_certs        : @semiring_certificates S
; selective_dioid_ast          : ast_selective_dioid
}.


Record prelattice {S : Type} := {
  prelattice_eqv           : @eqv S 
; prelattice_join          : binary_op S 
; prelattice_meet          : binary_op S 
; prelattice_join_proofs   : @sg_CI_certificates S 
; prelattice_meet_proofs   : @sg_CI_certificates S 
; prelattice_id_ann_proofs : @id_ann_certificates S 
; prelattice_proofs        : @lattice_certificates S 
; prelattice_ast           : ast_prelattice
}.

Record distributive_prelattice {S : Type} := {
  distributive_prelattice_eqv           : @eqv S 
; distributive_prelattice_join          : binary_op S 
; distributive_prelattice_meet          : binary_op S 
; distributive_prelattice_join_certs    : @sg_CI_certificates S 
; distributive_prelattice_meet_certs    : @sg_CI_certificates S 
; distributive_prelattice_id_ann_certs  : @id_ann_certificates S
; distributive_prelattice_certs         : @distributive_lattice_certificates S
; distributive_prelattice_ast           : ast_distributive_prelattice
}.

Record selective_distributive_prelattice {S : Type} := {
  selective_distributive_prelattice_eqv          : @eqv S 
; selective_distributive_prelattice_join         : binary_op S 
; selective_distributive_prelattice_meet         : binary_op S 
; selective_distributive_prelattice_join_certs   : @sg_CS_certificates S
; selective_distributive_prelattice_meet_certs   : @sg_CS_certificates S 
; selective_distributive_prelattice_id_ann_certs : @id_ann_certificates S
; selective_distributive_prelattice_certs        : @distributive_lattice_certificates S
; selective_distributive_prelattice_ast          : ast_selective_distributive_prelattice
}.

Record lattice {S : Type} := {
  lattice_eqv          : @eqv S 
; lattice_join         : binary_op S 
; lattice_meet         : binary_op S 
; lattice_join_certs   : @sg_CI_certificates S 
; lattice_meet_certs   : @sg_CI_certificates S
; lattice_id_ann_certs : @bounded_certificates S
; lattice_certs        : @lattice_certificates S
; lattice_ast          : ast_lattice
}.


Record distributive_lattice {S : Type} := {
  distributive_lattice_eqv          : @eqv S 
; distributive_lattice_join         : binary_op S 
; distributive_lattice_meet         : binary_op S 
; distributive_lattice_join_certs   : @sg_CI_certificates S 
; distributive_lattice_meet_certs   : @sg_CI_certificates S
; distributive_lattice_id_ann_certs : @bounded_certificates S
; distributive_lattice_certs        : @distributive_lattice_certificates S
; distributive_lattice_ast          : ast_distributive_lattice
}.


Record selective_distributive_lattice {S : Type} := {
  selective_distributive_lattice_eqv        : @eqv S 
; selective_distributive_lattice_join       : binary_op S 
; selective_distributive_lattice_meet       : binary_op S 
; selective_distributive_lattice_join_certs : @sg_CS_certificates S 
; selective_distributive_lattice_meet_certs : @sg_CS_certificates S
; selective_distributive_lattice_id_ann_certs : @bounded_certificates S                                                                  
; selective_distributive_lattice_certs      : @distributive_lattice_certificates S
; selective_distributive_lattice_ast        : ast_selective_distributive_lattice
}.


