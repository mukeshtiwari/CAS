Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.bs.properties.

(* bi-semigroups *) 



Section ACAS. 

Record id_ann_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_id_ann_exists_plus_id_d       : bop_exists_id_decidable S eq plus 
; A_id_ann_exists_plus_ann_d      : bop_exists_ann_decidable S eq plus 
; A_id_ann_exists_times_id_d      : bop_exists_id_decidable S eq times
; A_id_ann_exists_times_ann_d     : bop_exists_ann_decidable S eq times 
; A_id_ann_plus_id_is_times_ann_d : bops_id_equals_ann_decidable S eq plus times 
; A_id_ann_times_id_is_plus_ann_d : bops_id_equals_ann_decidable S eq times plus 
}.

Record zero_one_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_zero_one_exists_plus_ann_d      : bop_exists_ann_decidable S eq plus
; A_zero_one_exists_times_id        : bop_exists_id S eq times                                                         
; A_zero_one_plus_id_is_times_ann   : bops_id_equals_ann S eq plus times 
; A_zero_one_times_id_is_plus_ann_d : bops_id_equals_ann_decidable S eq times plus 
}.


Record with_one_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_with_one_exists_plus_id_d          : bop_exists_id_decidable S eq plus     
; A_with_one_exists_plus_ann           : bop_exists_ann S eq plus
; A_with_one_exists_times_id           : bop_exists_id S eq times
; A_with_one_exists_times_ann_d        : bop_exists_ann_decidable S eq times
; A_with_one_plus_id_is_times_ann_d    : bops_id_equals_ann_decidable S eq plus times                                                              
; A_with_one_times_id_is_plus_ann      : bops_id_equals_ann S eq times plus 
}.



Record bounded_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_bounded_plus_id_is_times_ann : bops_id_equals_ann S eq plus times 
; A_bounded_times_id_is_plus_ann : bops_id_equals_ann S eq times plus 
}.


(* hack? *) 
Record add_ann_mul_id_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_add_ann_mul_id_plus_id_d              : bop_exists_id_decidable S eq plus 
; A_add_ann_mul_id_plus_id_is_times_ann_d : bops_id_equals_ann_decidable S eq plus times 
; A_add_ann_mul_id_times_id_is_plus_ann   : bops_id_equals_ann S eq times plus
}.


Record bs_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_bs_left_distributive_d      : bop_left_distributive_decidable S eq plus times 
; A_bs_right_distributive_d     : bop_right_distributive_decidable S eq plus times 
; A_bs_left_left_absorptive_d   : bops_left_left_absorptive_decidable S eq plus times 
; A_bs_left_right_absorptive_d  : bops_left_right_absorptive_decidable S eq plus times 
; A_bs_right_left_absorptive_d  : bops_right_left_absorptive_decidable S eq plus times 
; A_bs_right_right_absorptive_d : bops_right_right_absorptive_decidable S eq plus times 

}.

Record semiring_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_semiring_left_distributive        : bop_left_distributive S eq plus times 
; A_semiring_right_distributive       : bop_right_distributive S eq plus times 
; A_semiring_left_left_absorptive_d   : bops_left_left_absorptive_decidable S eq plus times 
; A_semiring_left_right_absorptive_d  : bops_left_right_absorptive_decidable S eq plus times 
}.


Record path_algebra_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_path_algebra_left_distributive      : bop_left_distributive S eq plus times 
; A_path_algebra_right_distributive     : bop_right_distributive S eq plus times 
; A_path_algebra_left_left_absorptive   : bops_left_left_absorptive S eq plus times 
; A_path_algebra_left_right_absorptive  : bops_left_right_absorptive S eq plus times 
}.




Record lattice_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_lattice_absorptive           : bops_left_left_absorptive S eq plus times
; A_lattice_absorptive_dual      : bops_left_left_absorptive S eq times plus
; A_lattice_distributive_d       : bop_left_distributive_decidable S eq plus times
; A_lattice_distributive_dual_d  : bop_left_distributive_decidable S eq times plus (* required for lattice_dual  ? *)
}. 


Record distributive_lattice_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_distributive_lattice_absorptive        : bops_left_left_absorptive S eq plus times
; A_distributive_lattice_absorptive_dual   : bops_left_left_absorptive S eq times plus
; A_distributive_lattice_distributive      : bop_left_distributive S eq plus times
}. 

  

Record A_bs (S : Type) := {
  A_bs_eqv          : A_eqv S 
; A_bs_plus         : binary_op S 
; A_bs_times        : binary_op S 
; A_bs_plus_proofs   : asg_proofs S (A_eqv_eq S A_bs_eqv) A_bs_plus
; A_bs_times_proofs  : msg_proofs S (A_eqv_eq S A_bs_eqv) A_bs_times
; A_bs_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_bs_eqv) A_bs_plus A_bs_times                                 
; A_bs_proofs        : bs_proofs S (A_eqv_eq S A_bs_eqv) A_bs_plus A_bs_times
; A_bs_ast           : cas_ast
}.


Record A_bs_CS (S : Type) := {
  A_bs_CS_eqv           : A_eqv S 
; A_bs_CS_plus          : binary_op S 
; A_bs_CS_times         : binary_op S 
; A_bs_CS_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus
; A_bs_CS_times_proofs  : msg_proofs S    (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_times
; A_bs_CS_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus A_bs_CS_times
; A_bs_CS_proofs        : bs_proofs S (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus A_bs_CS_times
; A_bs_CS_ast           : cas_ast
}.

Record A_bs_CI (S : Type) := {
  A_bs_CI_eqv           : A_eqv S 
; A_bs_CI_plus          : binary_op S 
; A_bs_CI_times         : binary_op S 
; A_bs_CI_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_plus
; A_bs_CI_times_proofs  : msg_proofs S    (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_times
; A_bs_CI_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_plus A_bs_CI_times
; A_bs_CI_proofs        : bs_proofs S (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_plus A_bs_CI_times
; A_bs_CI_ast           : cas_ast
}.

Record A_presemiring (S : Type) := {
  A_presemiring_eqv           : A_eqv S 
; A_presemiring_plus          : binary_op S 
; A_presemiring_times         : binary_op S 
; A_presemiring_plus_proofs   : sg_C_proofs S (A_eqv_eq S A_presemiring_eqv) A_presemiring_plus
; A_presemiring_times_proofs  : msg_proofs S   (A_eqv_eq S A_presemiring_eqv) A_presemiring_times
; A_presemiring_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_presemiring_eqv) A_presemiring_plus A_presemiring_times
; A_presemiring_proofs        : semiring_proofs S (A_eqv_eq S A_presemiring_eqv) A_presemiring_plus A_presemiring_times
; A_presemiring_ast           : cas_ast
}.

Record A_selective_presemiring (S : Type) := {
  A_selective_presemiring_eqv           : A_eqv S 
; A_selective_presemiring_plus          : binary_op S 
; A_selective_presemiring_times         : binary_op S 
; A_selective_presemiring_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_presemiring_eqv) A_selective_presemiring_plus
; A_selective_presemiring_times_proofs  : msg_proofs S   (A_eqv_eq S A_selective_presemiring_eqv) A_selective_presemiring_times
; A_selective_presemiring_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_selective_presemiring_eqv) A_selective_presemiring_plus A_selective_presemiring_times
; A_selective_presemiring_proofs        : semiring_proofs S (A_eqv_eq S A_selective_presemiring_eqv) A_selective_presemiring_plus A_selective_presemiring_times
; A_selective_presemiring_ast           : cas_ast
}.


Record A_semiring (S : Type) := {
  A_semiring_eqv          : A_eqv S 
; A_semiring_plus         : binary_op S 
; A_semiring_times        : binary_op S 
; A_semiring_plus_proofs  : sg_C_proofs S (A_eqv_eq S A_semiring_eqv) A_semiring_plus
; A_semiring_times_proofs : msg_proofs S   (A_eqv_eq S A_semiring_eqv) A_semiring_times
; A_semiring_id_ann_proofs : zero_one_proofs S (A_eqv_eq S A_semiring_eqv) A_semiring_plus A_semiring_times
; A_semiring_proofs       : semiring_proofs S (A_eqv_eq S A_semiring_eqv) A_semiring_plus A_semiring_times
; A_semiring_ast          : cas_ast
}.

Record A_selective_semiring (S : Type) := {
  A_selective_semiring_eqv          : A_eqv S 
; A_selective_semiring_plus         : binary_op S 
; A_selective_semiring_times        : binary_op S 
; A_selective_semiring_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_plus
; A_selective_semiring_times_proofs : msg_proofs S   (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_times
; A_selective_semiring_id_ann_proofs : zero_one_proofs S (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_plus A_selective_semiring_times
; A_selective_semiring_proofs       : semiring_proofs S (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_plus A_selective_semiring_times
; A_selective_semiring_ast          : cas_ast
}.

Record A_pre_path_algebra (S : Type) := {
  A_pre_path_algebra_eqv           : A_eqv S 
; A_pre_path_algebra_plus          : binary_op S 
; A_pre_path_algebra_times         : binary_op S 
; A_pre_path_algebra_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_pre_path_algebra_eqv) A_pre_path_algebra_plus
; A_pre_path_algebra_times_proofs  : msg_proofs S   (A_eqv_eq S A_pre_path_algebra_eqv) A_pre_path_algebra_times
; A_pre_path_algebra_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_pre_path_algebra_eqv) A_pre_path_algebra_plus A_pre_path_algebra_times
; A_pre_path_algebra_proofs        : path_algebra_proofs S (A_eqv_eq S A_pre_path_algebra_eqv) A_pre_path_algebra_plus A_pre_path_algebra_times
; A_pre_path_algebra_ast           : cas_ast
}.


Record A_pre_path_algebra_NS (S : Type) := {
  A_pre_path_algebra_NS_eqv           : A_eqv S 
; A_pre_path_algebra_NS_plus          : binary_op S 
; A_pre_path_algebra_NS_times         : binary_op S 
; A_pre_path_algebra_NS_plus_proofs   : sg_CINS_proofs S (A_eqv_eq S A_pre_path_algebra_NS_eqv) A_pre_path_algebra_NS_plus
; A_pre_path_algebra_NS_times_proofs  : msg_proofs S   (A_eqv_eq S A_pre_path_algebra_NS_eqv) A_pre_path_algebra_NS_times
; A_pre_path_algebra_NS_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_pre_path_algebra_NS_eqv) A_pre_path_algebra_NS_plus A_pre_path_algebra_NS_times
; A_pre_path_algebra_NS_proofs        : path_algebra_proofs S (A_eqv_eq S A_pre_path_algebra_NS_eqv) A_pre_path_algebra_NS_plus A_pre_path_algebra_NS_times
; A_pre_path_algebra_NS_ast           : cas_ast
}.

Record A_pre_path_algebra_with_one (S : Type) := {
  A_pre_path_algebra_with_one_eqv           : A_eqv S 
; A_pre_path_algebra_with_one_plus          : binary_op S 
; A_pre_path_algebra_with_one_times         : binary_op S 
; A_pre_path_algebra_with_one_plus_proofs   : sg_CINS_proofs S (A_eqv_eq S A_pre_path_algebra_with_one_eqv) A_pre_path_algebra_with_one_plus
; A_pre_path_algebra_with_one_times_proofs  : msg_proofs S   (A_eqv_eq S A_pre_path_algebra_with_one_eqv) A_pre_path_algebra_with_one_times
; A_pre_path_algebra_with_one_id_ann_proofs : with_one_proofs S (A_eqv_eq S A_pre_path_algebra_with_one_eqv) A_pre_path_algebra_with_one_plus A_pre_path_algebra_with_one_times
; A_pre_path_algebra_with_one_proofs        : path_algebra_proofs S (A_eqv_eq S A_pre_path_algebra_with_one_eqv) A_pre_path_algebra_with_one_plus A_pre_path_algebra_with_one_times
; A_pre_path_algebra_with_one_ast           : cas_ast
}.


Record A_predioid_with_id (S : Type) := {
  A_pdwid_eqv           : A_eqv S 
; A_pdwid_plus          : binary_op S 
; A_pdwid_times         : binary_op S 
; A_pdwid_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_pdwid_eqv) A_pdwid_plus
; A_pdwid_times_proofs  : msg_proofs S   (A_eqv_eq S A_pdwid_eqv) A_pdwid_times
; A_pdwid_id_ann_proofs : add_ann_mul_id_proofs S (A_eqv_eq S A_pdwid_eqv) A_pdwid_plus A_pdwid_times
; A_pdwid_proofs        : semiring_proofs S (A_eqv_eq S A_pdwid_eqv) A_pdwid_plus A_pdwid_times
; A_pdwid_ast           : cas_ast
}.



Record A_dioid (S : Type) := {
  A_dioid_eqv           : A_eqv S 
; A_dioid_plus          : binary_op S 
; A_dioid_times         : binary_op S 
; A_dioid_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus
; A_dioid_times_proofs  : msg_proofs S   (A_eqv_eq S A_dioid_eqv) A_dioid_times
; A_dioid_id_ann_proofs : bounded_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus A_dioid_times
; A_dioid_proofs        : semiring_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus A_dioid_times
; A_dioid_ast           : cas_ast
}.

Record A_selective_dioid (S : Type) := {
  A_selective_dioid_eqv          : A_eqv S 
; A_selective_dioid_plus         : binary_op S 
; A_selective_dioid_times        : binary_op S 
; A_selective_dioid_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_plus
; A_selective_dioid_times_proofs : msg_proofs S   (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_times
; A_selective_dioid_id_ann_proofs : bounded_proofs S (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_plus A_selective_dioid_times
; A_selective_dioid_proofs       : semiring_proofs S (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_plus A_selective_dioid_times
; A_selective_dioid_ast          : cas_ast
}.



Record A_prelattice (S : Type) := {
  A_prelattice_eqv           : A_eqv S 
; A_prelattice_join          : binary_op S 
; A_prelattice_meet          : binary_op S 
; A_prelattice_join_proofs   : sg_CI_proofs S (A_eqv_eq S A_prelattice_eqv) A_prelattice_join
; A_prelattice_meet_proofs   : sg_CI_proofs S (A_eqv_eq S A_prelattice_eqv) A_prelattice_meet
; A_prelattice_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_prelattice_eqv) A_prelattice_join A_prelattice_meet      
; A_prelattice_proofs        : lattice_proofs S (A_eqv_eq S A_prelattice_eqv) A_prelattice_join A_prelattice_meet
; A_prelattice_ast           : cas_ast
}.

Record A_distributive_prelattice (S : Type) := {
  A_distributive_prelattice_eqv         : A_eqv S 
; A_distributive_prelattice_join        : binary_op S 
; A_distributive_prelattice_meet        : binary_op S 
; A_distributive_prelattice_join_proofs : sg_CI_proofs S (A_eqv_eq S A_distributive_prelattice_eqv) A_distributive_prelattice_join
; A_distributive_prelattice_meet_proofs : sg_CI_proofs S (A_eqv_eq S A_distributive_prelattice_eqv) A_distributive_prelattice_meet
; A_distributive_prelattice_id_ann_proofs : id_ann_proofs S
                                          (A_eqv_eq S A_distributive_prelattice_eqv)
                                          A_distributive_prelattice_join
                                          A_distributive_prelattice_meet                                                        
; A_distributive_prelattice_proofs      : distributive_lattice_proofs S
                                          (A_eqv_eq S A_distributive_prelattice_eqv)
                                          A_distributive_prelattice_join
                                          A_distributive_prelattice_meet
; A_distributive_prelattice_ast         : cas_ast
}.

Record A_selective_distributive_prelattice (S : Type) := {
  A_selective_distributive_prelattice_eqv         : A_eqv S 
; A_selective_distributive_prelattice_join        : binary_op S 
; A_selective_distributive_prelattice_meet        : binary_op S 
; A_selective_distributive_prelattice_join_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_prelattice_eqv) A_selective_distributive_prelattice_join
; A_selective_distributive_prelattice_meet_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_prelattice_eqv) A_selective_distributive_prelattice_meet
; A_selective_distributive_prelattice_id_ann_proofs : id_ann_proofs S
                                          (A_eqv_eq S A_selective_distributive_prelattice_eqv)
                                          A_selective_distributive_prelattice_join
                                          A_selective_distributive_prelattice_meet                                                                  
; A_selective_distributive_prelattice_proofs      : distributive_lattice_proofs S
                                          (A_eqv_eq S A_selective_distributive_prelattice_eqv)
                                          A_selective_distributive_prelattice_join
                                          A_selective_distributive_prelattice_meet
; A_selective_distributive_prelattice_ast         : cas_ast
}.


Record A_lattice (S : Type) := {
  A_lattice_eqv           : A_eqv S 
; A_lattice_join          : binary_op S 
; A_lattice_meet          : binary_op S 
; A_lattice_join_proofs   : sg_CI_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_join
; A_lattice_meet_proofs   : sg_CI_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_meet
; A_lattice_id_ann_proofs : bounded_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_join A_lattice_meet      
; A_lattice_proofs        : lattice_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_join A_lattice_meet
; A_lattice_ast           : cas_ast
}.

Record A_distributive_lattice (S : Type) := {
  A_distributive_lattice_eqv         : A_eqv S 
; A_distributive_lattice_join        : binary_op S 
; A_distributive_lattice_meet        : binary_op S 
; A_distributive_lattice_join_proofs : sg_CI_proofs S (A_eqv_eq S A_distributive_lattice_eqv) A_distributive_lattice_join
; A_distributive_lattice_meet_proofs : sg_CI_proofs S (A_eqv_eq S A_distributive_lattice_eqv) A_distributive_lattice_meet
; A_distributive_lattice_id_ann_proofs : bounded_proofs S
                                          (A_eqv_eq S A_distributive_lattice_eqv)
                                          A_distributive_lattice_join
                                          A_distributive_lattice_meet                                                        
; A_distributive_lattice_proofs      : distributive_lattice_proofs S
                                          (A_eqv_eq S A_distributive_lattice_eqv)
                                          A_distributive_lattice_join
                                          A_distributive_lattice_meet
; A_distributive_lattice_ast         : cas_ast
}.

Record A_selective_distributive_lattice (S : Type) := {
  A_selective_distributive_lattice_eqv         : A_eqv S 
; A_selective_distributive_lattice_join        : binary_op S 
; A_selective_distributive_lattice_meet        : binary_op S 
; A_selective_distributive_lattice_join_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_lattice_eqv) A_selective_distributive_lattice_join
; A_selective_distributive_lattice_meet_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_lattice_eqv) A_selective_distributive_lattice_meet
; A_selective_distributive_lattice_id_ann_proofs : bounded_proofs S
                                          (A_eqv_eq S A_selective_distributive_lattice_eqv)
                                          A_selective_distributive_lattice_join
                                          A_selective_distributive_lattice_meet                                                                  
; A_selective_distributive_lattice_proofs      : distributive_lattice_proofs S
                                          (A_eqv_eq S A_selective_distributive_lattice_eqv)
                                          A_selective_distributive_lattice_join
                                          A_selective_distributive_lattice_meet
; A_selective_distributive_lattice_ast         : cas_ast
}.

End ACAS. 

Section CAS.


Record id_ann_certificates {S: Type} := 
{
  id_ann_exists_plus_id_d       : @check_exists_id S 
; id_ann_exists_plus_ann_d      : @check_exists_ann S 
; id_ann_exists_times_id_d      : @check_exists_id S 
; id_ann_exists_times_ann_d     : @check_exists_ann S 
; id_ann_plus_id_is_times_ann_d : @check_plus_id_equals_times_ann S
; id_ann_times_id_is_plus_ann_d : @check_times_id_equals_plus_ann S
}.

Record zero_one_certificates {S: Type} := 
{
  zero_one_exists_plus_ann_d      : @check_exists_ann S 
; zero_one_exists_times_id        : @assert_exists_id S 
; zero_one_plus_id_is_times_ann   : @assert_plus_id_equals_times_ann S
; zero_one_times_id_is_plus_ann_d : @check_times_id_equals_plus_ann S
}.

Record with_one_certs {S: Type} := 
{
  with_one_exists_plus_id_d          : @check_exists_id S 
; with_one_exists_plus_ann           : @assert_exists_ann S 
; with_one_exists_times_id           : @assert_exists_id S 
; with_one_exists_times_ann_d        : @check_exists_ann S 
; with_one_plus_id_is_times_ann_d    : @check_plus_id_equals_times_ann S
; with_one_times_id_is_plus_ann      : @assert_times_id_equals_plus_ann S
}.



Record bounded_certificates {S: Type} := 
{
  bounded_plus_id_is_times_ann : @assert_plus_id_equals_times_ann S
; bounded_times_id_is_plus_ann : @assert_times_id_equals_plus_ann S
}.


Record bs_certificates {S: Type} := 
{
  bs_left_distributive_d      : check_left_distributive (S := S) 
; bs_right_distributive_d     : check_right_distributive (S := S) 
; bs_left_left_absorptive_d   : check_left_left_absorptive (S := S) 
; bs_left_right_absorptive_d  : check_left_right_absorptive (S := S) 
; bs_right_left_absorptive_d  : check_right_left_absorptive (S := S) 
; bs_right_right_absorptive_d : check_right_right_absorptive (S := S) 
}. 


Record path_algebra_certs {S: Type} := 
{
  path_algebra_left_distributive      : @assert_left_distributive S 
; path_algebra_right_distributive     : @assert_right_distributive S 
; path_algebra_left_left_absorptive   : @assert_left_left_absorptive S 
; path_algebra_left_right_absorptive  : @assert_left_right_absorptive S 
}.


Record semiring_certificates {S: Type} := 
{
  semiring_left_distributive      : @assert_left_distributive S
; semiring_right_distributive     : @assert_right_distributive S

; semiring_left_left_absorptive_d   : @check_left_left_absorptive S
; semiring_left_right_absorptive_d  : @check_left_right_absorptive S 
}.

Record lattice_certificates {S: Type} := 
{
  lattice_absorptive           : @assert_left_left_absorptive S 
; lattice_absorptive_dual      : @assert_left_left_absorptive_dual S 
 
; lattice_distributive_d       : @check_left_distributive S 
; lattice_distributive_dual_d  : @check_left_distributive_dual S 
}. 

Record distributive_lattice_certificates {S: Type} := 
{
  distributive_lattice_absorptive        : @assert_left_left_absorptive S 
; distributive_lattice_absorptive_dual   : @assert_left_left_absorptive_dual S 
; distributive_lattice_distributive      : @assert_left_distributive S 
}. 


  
Record bs {S : Type} := {
  bs_eqv           : eqv (S := S) 
; bs_plus          : binary_op S 
; bs_times         : binary_op S 
; bs_plus_certs    : asg_certificates (S := S) 
; bs_times_certs   : msg_certificates (S := S)
; bs_id_ann_certs  : id_ann_certificates (S := S)
; bs_certs         : bs_certificates (S := S)
; bs_ast           : cas_ast
}.


Record bs_CS {S : Type} := {
  bs_CS_eqv          : eqv (S := S) 
; bs_CS_plus         : binary_op S 
; bs_CS_times        : binary_op S 
; bs_CS_plus_certs   : sg_CS_certificates (S := S) 
; bs_CS_times_certs  : msg_certificates (S := S)
; bs_CS_id_ann_certs : id_ann_certificates (S := S) 
; bs_CS_certs        : bs_certificates (S := S)
; bs_CS_ast          : cas_ast
}.

Record bs_CI {S : Type} := {
  bs_CI_eqv          : eqv (S := S) 
; bs_CI_plus         : binary_op S 
; bs_CI_times        : binary_op S 
; bs_CI_plus_certs   : sg_CI_certificates (S := S) 
; bs_CI_times_certs  : msg_certificates (S := S)
; bs_CI_id_ann_certs : id_ann_certificates (S := S)               
; bs_CI_certs        : bs_certificates (S := S)
; bs_CI_ast          : cas_ast
}.


Record pre_path_algebra {S : Type} := {
  pre_path_algebra_eqv          : @eqv S 
; pre_path_algebra_plus         : @binary_op S 
; pre_path_algebra_times        : @binary_op S 
; pre_path_algebra_plus_certs   : @sg_CI_certificates S 
; pre_path_algebra_times_certs  : @msg_certificates S 
; pre_path_algebra_id_ann_certs : @id_ann_certificates S 
; pre_path_algebra_certs        : @path_algebra_certs S 
; pre_path_algebra_ast          : cas_ast
}.

Record pre_path_algebra_NS {S : Type} := {
  pre_path_algebra_NS_eqv          : @eqv S 
; pre_path_algebra_NS_plus         : @binary_op S 
; pre_path_algebra_NS_times        : @binary_op S 
; pre_path_algebra_NS_plus_certs   : @sg_CINS_certificates S 
; pre_path_algebra_NS_times_certs  : @msg_certificates S 
; pre_path_algebra_NS_id_ann_certs : @id_ann_certificates S 
; pre_path_algebra_NS_certs        : @path_algebra_certs S 
; pre_path_algebra_NS_ast          : cas_ast
}.


Record pre_path_algebra_with_one {S : Type} := {
  pre_path_algebra_with_one_eqv          : @eqv S 
; pre_path_algebra_with_one_plus         : @binary_op S 
; pre_path_algebra_with_one_times        : @binary_op S 
; pre_path_algebra_with_one_plus_certs   : @sg_CINS_certificates S 
; pre_path_algebra_with_one_times_certs  : @msg_certificates S 
; pre_path_algebra_with_one_id_ann_certs : @with_one_certs S 
; pre_path_algebra_with_one_certs        : @path_algebra_certs S 
; pre_path_algebra_with_one_ast          : cas_ast
}.



Record presemiring {S : Type} := {
  presemiring_eqv          : @eqv S 
; presemiring_plus         : binary_op S 
; presemiring_times        : binary_op S 
; presemiring_plus_certs   : @sg_C_certificates S 
; presemiring_times_certs  : @msg_certificates S
; presemiring_id_ann_certs : @id_ann_certificates S
; presemiring_certs        : @semiring_certificates S
; presemiring_ast          : cas_ast
}.

Record selective_presemiring {S : Type} := {
  selective_presemiring_eqv          : @eqv S 
; selective_presemiring_plus         : binary_op S 
; selective_presemiring_times        : binary_op S 
; selective_presemiring_plus_certs   : @sg_CS_certificates S 
; selective_presemiring_times_certs  : @msg_certificates S
; selective_presemiring_id_ann_certs : @id_ann_certificates S
; selective_presemiring_certs        : @semiring_certificates S
; selective_presemiring_ast          : cas_ast
}.



Record semiring {S : Type} := {
  semiring_eqv          : @eqv S 
; semiring_plus         : binary_op S 
; semiring_times        : binary_op S 
; semiring_plus_certs   : @sg_C_certificates S 
; semiring_times_certs  : @msg_certificates S
; semiring_id_ann_certs : @zero_one_certificates S
; semiring_certs        : @semiring_certificates S
; semiring_ast          : cas_ast
}.


Record selective_semiring {S : Type} := {
  selective_semiring_eqv          : @eqv S 
; selective_semiring_plus         : binary_op S 
; selective_semiring_times        : binary_op S 
; selective_semiring_plus_certs   : @sg_CS_certificates S 
; selective_semiring_times_certs  : @msg_certificates S
; selective_semiring_id_ann_certs : @zero_one_certificates S
; selective_semiring_certs        : @semiring_certificates S
; selective_semiring_ast          : cas_ast
}.

Record dioid {S : Type} := {
  dioid_eqv          : @eqv S 
; dioid_plus         : binary_op S 
; dioid_times        : binary_op S 
; dioid_plus_certs   : @sg_CI_certificates S 
; dioid_times_certs  : @msg_certificates S
; dioid_id_ann_certs : @bounded_certificates S
; dioid_certs        : @semiring_certificates S
; dioid_ast          : cas_ast
}.

Record selective_dioid {S : Type} := {
  selective_dioid_eqv          : @eqv S 
; selective_dioid_plus         : binary_op S 
; selective_dioid_times        : binary_op S 
; selective_dioid_plus_certs   : @sg_CS_certificates S 
; selective_dioid_times_certs  : @msg_certificates S
; selective_dioid_id_ann_certs : @bounded_certificates S                  
; selective_dioid_certs        : @semiring_certificates S
; selective_dioid_ast          : cas_ast
}.


Record prelattice {S : Type} := {
  prelattice_eqv           : @eqv S 
; prelattice_join          : binary_op S 
; prelattice_meet          : binary_op S 
; prelattice_join_proofs   : @sg_CI_certificates S 
; prelattice_meet_proofs   : @sg_CI_certificates S 
; prelattice_id_ann_proofs : @id_ann_certificates S 
; prelattice_proofs        : @lattice_certificates S 
; prelattice_ast           : cas_ast
}.

Record distributive_prelattice {S : Type} := {
  distributive_prelattice_eqv           : @eqv S 
; distributive_prelattice_join          : binary_op S 
; distributive_prelattice_meet          : binary_op S 
; distributive_prelattice_join_certs    : @sg_CI_certificates S 
; distributive_prelattice_meet_certs    : @sg_CI_certificates S 
; distributive_prelattice_id_ann_certs  : @id_ann_certificates S
; distributive_prelattice_certs         : @distributive_lattice_certificates S
; distributive_prelattice_ast           : cas_ast
}.

Record selective_distributive_prelattice {S : Type} := {
  selective_distributive_prelattice_eqv          : @eqv S 
; selective_distributive_prelattice_join         : binary_op S 
; selective_distributive_prelattice_meet         : binary_op S 
; selective_distributive_prelattice_join_certs   : @sg_CS_certificates S
; selective_distributive_prelattice_meet_certs   : @sg_CS_certificates S 
; selective_distributive_prelattice_id_ann_certs : @id_ann_certificates S
; selective_distributive_prelattice_certs        : @distributive_lattice_certificates S
; selective_distributive_prelattice_ast          : cas_ast
}.

Record lattice {S : Type} := {
  lattice_eqv          : @eqv S 
; lattice_join         : binary_op S 
; lattice_meet         : binary_op S 
; lattice_join_certs   : @sg_CI_certificates S 
; lattice_meet_certs   : @sg_CI_certificates S
; lattice_id_ann_certs : @bounded_certificates S
; lattice_certs        : @lattice_certificates S
; lattice_ast          : cas_ast
}.


Record distributive_lattice {S : Type} := {
  distributive_lattice_eqv          : @eqv S 
; distributive_lattice_join         : binary_op S 
; distributive_lattice_meet         : binary_op S 
; distributive_lattice_join_certs   : @sg_CI_certificates S 
; distributive_lattice_meet_certs   : @sg_CI_certificates S
; distributive_lattice_id_ann_certs : @bounded_certificates S
; distributive_lattice_certs        : @distributive_lattice_certificates S
; distributive_lattice_ast          : cas_ast
}.


Record selective_distributive_lattice {S : Type} := {
  selective_distributive_lattice_eqv        : @eqv S 
; selective_distributive_lattice_join       : binary_op S 
; selective_distributive_lattice_meet       : binary_op S 
; selective_distributive_lattice_join_certs : @sg_CS_certificates S 
; selective_distributive_lattice_meet_certs : @sg_CS_certificates S
; selective_distributive_lattice_id_ann_certs : @bounded_certificates S                                                                  
; selective_distributive_lattice_certs      : @distributive_lattice_certificates S
; selective_distributive_lattice_ast        : cas_ast
}.



  
End CAS. 

Section Translation. 

Definition P2C_id_ann : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
             id_ann_proofs S r b1 b2 -> @id_ann_certificates S 
:= λ S r b1 b2 R,
{|
  id_ann_exists_plus_id_d       := p2c_exists_id_check S r b1  (A_id_ann_exists_plus_id_d S r b1 b2 R)
; id_ann_exists_plus_ann_d      := p2c_exists_ann_check S r b1  (A_id_ann_exists_plus_ann_d S r b1 b2 R)
; id_ann_exists_times_id_d      := p2c_exists_id_check S r b2  (A_id_ann_exists_times_id_d S r b1 b2 R)
; id_ann_exists_times_ann_d     := p2c_exists_ann_check S r b2  (A_id_ann_exists_times_ann_d S r b1 b2 R)
; id_ann_plus_id_is_times_ann_d := p2c_plus_id_equals_times_ann S r b1 b2 (A_id_ann_plus_id_is_times_ann_d S r b1 b2 R)
; id_ann_times_id_is_plus_ann_d := p2c_times_id_equals_plus_ann S r b1 b2  (A_id_ann_times_id_is_plus_ann_d S r b1 b2 R)
|}.


Definition P2C_zero_one : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
             zero_one_proofs S r b1 b2 -> @zero_one_certificates S 
:= λ S r b1 b2 R,
{|
  zero_one_exists_plus_ann_d      := p2c_exists_ann_check S r b1  (A_zero_one_exists_plus_ann_d S r b1 b2 R)
; zero_one_exists_times_id        := p2c_exists_id_assert S r b2  (A_zero_one_exists_times_id S r b1 b2 R)
; zero_one_plus_id_is_times_ann   := p2c_plus_id_equals_times_ann_assert S r b1 b2 (A_zero_one_plus_id_is_times_ann S r b1 b2 R)
; zero_one_times_id_is_plus_ann_d := p2c_times_id_equals_plus_ann S r b1 b2  (A_zero_one_times_id_is_plus_ann_d S r b1 b2 R)
|}.


Definition P2C_bounded : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
             bounded_proofs S r b1 b2 -> @bounded_certificates S 
:= λ S r b1 b2 R,
{|
  bounded_plus_id_is_times_ann  := p2c_plus_id_equals_times_ann_assert S r b1 b2 (A_bounded_plus_id_is_times_ann S r b1 b2 R)
; bounded_times_id_is_plus_ann := p2c_times_id_equals_plus_ann_assert S r b1 b2  (A_bounded_times_id_is_plus_ann S r b1 b2 R)
|}.



Definition P2C_bs : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
             bs_proofs S r b1 b2 -> @bs_certificates S 
:= λ S r b1 b2 R,
{|
  bs_left_distributive_d      := p2c_left_distributive S r b1 b2 (A_bs_left_distributive_d S r b1 b2 R)
; bs_right_distributive_d     := p2c_right_distributive S r b1 b2 (A_bs_right_distributive_d S r b1 b2 R)

; bs_left_left_absorptive_d   := p2c_left_left_absorptive S r b1 b2 (A_bs_left_left_absorptive_d S r b1 b2 R)
; bs_left_right_absorptive_d  := p2c_left_right_absorptive S r b1 b2 (A_bs_left_right_absorptive_d S r b1 b2 R)
; bs_right_left_absorptive_d  := p2c_right_left_absorptive S r b1 b2 (A_bs_right_left_absorptive_d S r b1 b2 R)
; bs_right_right_absorptive_d := p2c_right_right_absorptive S r b1 b2 (A_bs_right_right_absorptive_d S r b1 b2 R)
|}. 

Definition A2C_bs : ∀ (S : Type), A_bs S -> @bs S 
:= λ S R,
{|
 bs_eqv         := A2C_eqv S (A_bs_eqv S R)
; bs_plus        := A_bs_plus S R 
; bs_times       := A_bs_times S R 
; bs_plus_certs  := P2C_asg S (A_eqv_eq S (A_bs_eqv S R)) 
                                (A_bs_plus S R) 
                                (A_bs_plus_proofs S R)
; bs_times_certs := P2C_msg S (A_eqv_eq S (A_bs_eqv S R)) 
                                (A_bs_times S R) 
                                (A_bs_times_proofs S R)
; bs_id_ann_certs := P2C_id_ann S (A_eqv_eq S (A_bs_eqv S R)) 
                                   (A_bs_plus S R) 
                                   (A_bs_times S R) 
                                   (A_bs_id_ann_proofs S R)
; bs_certs       := P2C_bs S (A_eqv_eq S (A_bs_eqv S R)) 
                                   (A_bs_plus S R) 
                                   (A_bs_times S R) 
                                   (A_bs_proofs S R)
; bs_ast        := A_bs_ast S R
|}.



Definition A2C_bs_CS : ∀ (S : Type), A_bs_CS S -> @bs_CS S 
:= λ S R,
{|
  bs_CS_eqv         := A2C_eqv S (A_bs_CS_eqv S R)
; bs_CS_plus        := A_bs_CS_plus S R 
; bs_CS_times       := A_bs_CS_times S R 
; bs_CS_plus_certs  := P2C_sg_CS S (A_eqv_eq S (A_bs_CS_eqv S R)) 
                                (A_bs_CS_plus S R) 
                                (A_bs_CS_plus_proofs S R)
; bs_CS_times_certs := P2C_msg S (A_eqv_eq S (A_bs_CS_eqv S R)) 
                                (A_bs_CS_times S R) 
                                (A_bs_CS_times_proofs S R)
; bs_CS_id_ann_certs := P2C_id_ann S (A_eqv_eq S (A_bs_CS_eqv S R)) 
                                   (A_bs_CS_plus S R) 
                                   (A_bs_CS_times S R) 
                                   (A_bs_CS_id_ann_proofs S R)
; bs_CS_certs       := P2C_bs S (A_eqv_eq S (A_bs_CS_eqv S R)) 
                                   (A_bs_CS_plus S R) 
                                   (A_bs_CS_times S R) 
                                   (A_bs_CS_proofs S R)
; bs_CS_ast        := A_bs_CS_ast S R
|}.


Definition A2C_bs_CI : ∀ (S : Type), A_bs_CI S -> @bs_CI S 
:= λ S R,
{|
  bs_CI_eqv         := A2C_eqv S (A_bs_CI_eqv S R)
; bs_CI_plus        := A_bs_CI_plus S R 
; bs_CI_times       := A_bs_CI_times S R 
; bs_CI_plus_certs  := P2C_sg_CI S (A_eqv_eq S (A_bs_CI_eqv S R)) 
                                (A_bs_CI_plus S R) 
                                (A_bs_CI_plus_proofs S R)
; bs_CI_times_certs := P2C_msg S (A_eqv_eq S (A_bs_CI_eqv S R)) 
                                (A_bs_CI_times S R) 
                                (A_bs_CI_times_proofs S R)
; bs_CI_id_ann_certs := P2C_id_ann S (A_eqv_eq S (A_bs_CI_eqv S R)) 
                                   (A_bs_CI_plus S R) 
                                   (A_bs_CI_times S R) 
                                   (A_bs_CI_id_ann_proofs S R)
; bs_CI_certs       := P2C_bs S (A_eqv_eq S (A_bs_CI_eqv S R)) 
                                   (A_bs_CI_plus S R) 
                                   (A_bs_CI_times S R) 
                                   (A_bs_CI_proofs S R)
; bs_CI_ast        := A_bs_CI_ast S R
|}.


(* for downcasting *) 

Definition P2C_sg_option : ∀ (S : Type) (r : brel S) (b : binary_op S), option(sg_proofs S r b) -> option(@sg_certificates S)
  := λ S r b, option_map (P2C_sg S r b). 


Definition A2C_sg_option : ∀ (S : Type), option(A_sg S) -> option(@sg S)
  := λ S, option_map (A2C_sg S). 

Definition P2C_sg_C_option : ∀ (S : Type) (r : brel S) (b : binary_op S),  option(sg_C_proofs S r b) -> option(@sg_C_certificates S)       
  := λ S r b, option_map (P2C_sg_C S r b). 

Definition A2C_sg_C_option : ∀ (S : Type), option(A_sg_C S) -> option(@sg_C S) 
  := λ S, option_map (A2C_sg_C S). 

Definition P2C_sg_CI_option : ∀ (S : Type) (r : brel S) (b : binary_op S), option(sg_CI_proofs S r b) -> option(@sg_CI_certificates S)  
  := λ S r b, option_map (P2C_sg_CI S r b).          

Definition A2C_sg_CI_option : ∀ (S : Type), option(A_sg_CI S) -> option(@sg_CI S) 
  := λ S, option_map (A2C_sg_CI S). 

Definition P2C_sg_CS_option : ∀ (S : Type) (r : brel S) (b : binary_op S), option(sg_CS_proofs S r b) -> option(@sg_CS_certificates S)   
  := λ S r b, option_map (P2C_sg_CS S r b). 
         
Definition A2C_sg_CS_option : ∀ (S : Type), option(A_sg_CS S) -> option(@sg_CS S)
  := λ S, option_map (A2C_sg_CS S). 


Definition P2C_sg_CK_option : ∀ (S : Type) (r : brel S) (b : binary_op S), option(sg_CK_proofs S r b) -> option(@sg_CK_certificates S)   
  := λ S r b, option_map (P2C_sg_CK S r b). 
         
Definition A2C_sg_CK_option : ∀ (S : Type), option(A_sg_CK S) -> option(@sg_CK S)
  := λ S, option_map (A2C_sg_CK S). 



(* 
Definition P2C_po_option : ∀ (S : Type) (eq lte : brel S), option(po_proofs S eq lte) -> option(po_certs S) 
  := λ S r b, option_map (P2C_po S r b). 

Definition A2C_po_option : ∀ (S : Type), option(A_po S) -> option(po S) 
  := λ S, option_map (A2C_po S). 

Definition P2C_to_option : ∀ (S : Type) (eq lte : brel S), option(to_proofs S eq lte) -> option(to_certs S)
  := λ S eq lte, option_map (P2C_to S eq lte). 

Definition A2C_to_option : ∀ (S : Type), option(A_to S) -> option(to S) 
  := λ S, option_map (A2C_to S). 



Definition P2C_bs_option : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), option(bs_proofs S r b1 b2) -> option(bs_certs S)
  := λ S r b1 b2, option_map (P2C_bs S r b1 b2). 

Definition A2C_bs_option : ∀ (S : Type), option(A_bs S) -> option(bs S) 
  := λ S, option_map (A2C_bs S). 

Definition P2C_sr_option : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),  option(sr_proofs S r b1 b2) -> option(sr_certs S) 
  := λ S r b1 b2, option_map (P2C_sr S r b1 b2). 

Definition A2C_sr_option : ∀ (S : Type), option(A_sr S) -> option(sr S) 
  := λ S, option_map (A2C_sr S). 

Definition P2C_csr_option : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), option(csr_proofs S r b1 b2) -> option(csr_certs S)
  := λ S r b1 b2, option_map (P2C_csr S r b1 b2). 
               
Definition A2C_csr_option : ∀ (S : Type), option(A_csr S) -> option(csr S) 
  := λ S, option_map (A2C_csr S). 

Definition A2C_pa_option : ∀ (S : Type), option (A_pa S) -> option (pa S)
  := λ S, option_map (A2C_pa S). 


 *)



Definition P2C_semiring : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
             semiring_proofs S r b1 b2 -> @semiring_certificates S 
:= λ S r b1 b2 R,
{|
  semiring_left_distributive      := Assert_Left_Distributive
; semiring_right_distributive     := Assert_Right_Distributive

; semiring_left_left_absorptive_d   := p2c_left_left_absorptive S r b1 b2 (A_semiring_left_left_absorptive_d S r b1 b2 R)
; semiring_left_right_absorptive_d  := p2c_left_right_absorptive S r b1 b2 (A_semiring_left_right_absorptive_d S r b1 b2 R)

|}.



Definition A2C_presemiring : ∀ (S : Type), A_presemiring S -> @presemiring S 
:= λ S R,
{|
  presemiring_eqv         := A2C_eqv S (A_presemiring_eqv S R)
; presemiring_plus        := A_presemiring_plus S R 
; presemiring_times       := A_presemiring_times S R 
; presemiring_plus_certs  := P2C_sg_C S (A_eqv_eq S (A_presemiring_eqv S R)) 
                                (A_presemiring_plus S R) 
                                (A_presemiring_plus_proofs S R)
; presemiring_times_certs := P2C_msg S (A_eqv_eq S (A_presemiring_eqv S R)) 
                                (A_presemiring_times S R) 
                                (A_presemiring_times_proofs S R)
; presemiring_id_ann_certs := P2C_id_ann S (A_eqv_eq S (A_presemiring_eqv S R)) 
                                   (A_presemiring_plus S R) 
                                   (A_presemiring_times S R) 
                                   (A_presemiring_id_ann_proofs S R)        
; presemiring_certs       := P2C_semiring S (A_eqv_eq S (A_presemiring_eqv S R)) 
                                   (A_presemiring_plus S R) 
                                   (A_presemiring_times S R) 
                                   (A_presemiring_proofs S R)
; presemiring_ast        := A_presemiring_ast S R
|}.

Definition A2C_selective_presemiring : ∀ (S : Type), A_selective_presemiring S -> @selective_presemiring S 
:= λ S R,
{|
  selective_presemiring_eqv         := A2C_eqv S (A_selective_presemiring_eqv S R)
; selective_presemiring_plus        := A_selective_presemiring_plus S R 
; selective_presemiring_times       := A_selective_presemiring_times S R 
; selective_presemiring_plus_certs  := P2C_sg_CS S (A_eqv_eq S (A_selective_presemiring_eqv S R)) 
                                (A_selective_presemiring_plus S R) 
                                (A_selective_presemiring_plus_proofs S R)
; selective_presemiring_times_certs := P2C_msg S (A_eqv_eq S (A_selective_presemiring_eqv S R)) 
                                (A_selective_presemiring_times S R) 
                                (A_selective_presemiring_times_proofs S R)
; selective_presemiring_id_ann_certs := P2C_id_ann S (A_eqv_eq S (A_selective_presemiring_eqv S R)) 
                                   (A_selective_presemiring_plus S R) 
                                   (A_selective_presemiring_times S R) 
                                   (A_selective_presemiring_id_ann_proofs S R)        
; selective_presemiring_certs       := P2C_semiring S (A_eqv_eq S (A_selective_presemiring_eqv S R)) 
                                   (A_selective_presemiring_plus S R) 
                                   (A_selective_presemiring_times S R) 
                                   (A_selective_presemiring_proofs S R)
; selective_presemiring_ast        := A_selective_presemiring_ast S R
|}.




Definition A2C_semiring : ∀ (S : Type), A_semiring S -> @semiring S 
:= λ S R,
{|
  semiring_eqv         := A2C_eqv S (A_semiring_eqv S R)
; semiring_plus        := A_semiring_plus S R 
; semiring_times       := A_semiring_times S R 
; semiring_plus_certs  := P2C_sg_C S (A_eqv_eq S (A_semiring_eqv S R)) 
                                (A_semiring_plus S R) 
                                (A_semiring_plus_proofs S R)
; semiring_times_certs := P2C_msg S (A_eqv_eq S (A_semiring_eqv S R)) 
                                (A_semiring_times S R) 
                                (A_semiring_times_proofs S R)
; semiring_id_ann_certs := P2C_zero_one S (A_eqv_eq S (A_semiring_eqv S R)) 
                                   (A_semiring_plus S R) 
                                   (A_semiring_times S R) 
                                   (A_semiring_id_ann_proofs S R)         
; semiring_certs       := P2C_semiring S (A_eqv_eq S (A_semiring_eqv S R)) 
                                   (A_semiring_plus S R) 
                                   (A_semiring_times S R) 
                                   (A_semiring_proofs S R)
; semiring_ast        := A_semiring_ast S R
|}.

Definition A2C_selective_semiring : ∀ (S : Type), A_selective_semiring S -> @selective_semiring S 
:= λ S R,
{|
  selective_semiring_eqv         := A2C_eqv S (A_selective_semiring_eqv S R)
; selective_semiring_plus        := A_selective_semiring_plus S R 
; selective_semiring_times       := A_selective_semiring_times S R 
; selective_semiring_plus_certs  := P2C_sg_CS S (A_eqv_eq S (A_selective_semiring_eqv S R)) 
                                (A_selective_semiring_plus S R) 
                                (A_selective_semiring_plus_proofs S R)
; selective_semiring_times_certs := P2C_msg S (A_eqv_eq S (A_selective_semiring_eqv S R)) 
                                (A_selective_semiring_times S R) 
                                (A_selective_semiring_times_proofs S R)
; selective_semiring_id_ann_certs := P2C_zero_one S (A_eqv_eq S (A_selective_semiring_eqv S R)) 
                                   (A_selective_semiring_plus S R) 
                                   (A_selective_semiring_times S R) 
                                   (A_selective_semiring_id_ann_proofs S R)         
; selective_semiring_certs       := P2C_semiring S (A_eqv_eq S (A_selective_semiring_eqv S R)) 
                                   (A_selective_semiring_plus S R) 
                                   (A_selective_semiring_times S R) 
                                   (A_selective_semiring_proofs S R)
; selective_semiring_ast        := A_selective_semiring_ast S R
|}.


Definition A2C_dioid : ∀ (S : Type), A_dioid S -> @dioid S 
:= λ S R,
{|
  dioid_eqv         := A2C_eqv S (A_dioid_eqv S R)
; dioid_plus        := A_dioid_plus S R 
; dioid_times       := A_dioid_times S R 
; dioid_plus_certs  := P2C_sg_CI S (A_eqv_eq S (A_dioid_eqv S R)) 
                                (A_dioid_plus S R) 
                                (A_dioid_plus_proofs S R)
; dioid_times_certs := P2C_msg S (A_eqv_eq S (A_dioid_eqv S R)) 
                                (A_dioid_times S R) 
                                (A_dioid_times_proofs S R)
; dioid_id_ann_certs := P2C_bounded S (A_eqv_eq S (A_dioid_eqv S R)) 
                                   (A_dioid_plus S R) 
                                   (A_dioid_times S R) 
                                   (A_dioid_id_ann_proofs S R)
; dioid_certs       := P2C_semiring S (A_eqv_eq S (A_dioid_eqv S R)) 
                                   (A_dioid_plus S R) 
                                   (A_dioid_times S R) 
                                   (A_dioid_proofs S R)
; dioid_ast        := A_dioid_ast S R
|}.


Definition A2C_selective_dioid : ∀ (S : Type), A_selective_dioid S -> @selective_dioid S 
:= λ S R,
{|
  selective_dioid_eqv         := A2C_eqv S (A_selective_dioid_eqv S R)
; selective_dioid_plus        := A_selective_dioid_plus S R 
; selective_dioid_times       := A_selective_dioid_times S R 
; selective_dioid_plus_certs  := P2C_sg_CS S (A_eqv_eq S (A_selective_dioid_eqv S R)) 
                                (A_selective_dioid_plus S R) 
                                (A_selective_dioid_plus_proofs S R)
; selective_dioid_times_certs := P2C_msg S (A_eqv_eq S (A_selective_dioid_eqv S R)) 
                                (A_selective_dioid_times S R) 
                                (A_selective_dioid_times_proofs S R)
; selective_dioid_id_ann_certs := P2C_bounded S (A_eqv_eq S (A_selective_dioid_eqv S R)) 
                                   (A_selective_dioid_plus S R) 
                                   (A_selective_dioid_times S R) 
                                   (A_selective_dioid_id_ann_proofs S R)              
; selective_dioid_certs       := P2C_semiring S (A_eqv_eq S (A_selective_dioid_eqv S R)) 
                                   (A_selective_dioid_plus S R) 
                                   (A_selective_dioid_times S R) 
                                   (A_selective_dioid_proofs S R)  
; selective_dioid_ast        := A_selective_dioid_ast S R
|}.




Definition P2C_lattice : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
             lattice_proofs S r b1 b2 -> @lattice_certificates S 
:= λ S r b1 b2 R,
{|

  lattice_absorptive             := Assert_Left_Left_Absorptive
; lattice_absorptive_dual        := Assert_Left_Left_Absorptive_Dual 

; lattice_distributive_d         := p2c_left_distributive S r b1 b2 (A_lattice_distributive_d S r b1 b2 R)
; lattice_distributive_dual_d    := p2c_left_distributive_dual S r b1 b2 (A_lattice_distributive_dual_d S r b1 b2 R)

|}. 

Definition A2C_lattice : ∀ (S : Type), A_lattice S -> @lattice S 
:= λ S R,
{|
  lattice_eqv         := A2C_eqv S (A_lattice_eqv S R)
; lattice_join        := A_lattice_join S R 
; lattice_meet        := A_lattice_meet S R 
; lattice_join_certs  := P2C_sg_CI S (A_eqv_eq S (A_lattice_eqv S R)) 
                                (A_lattice_join S R) 
                                (A_lattice_join_proofs S R)
; lattice_meet_certs := P2C_sg_CI S (A_eqv_eq S (A_lattice_eqv S R)) 
                                (A_lattice_meet S R) 
                                (A_lattice_meet_proofs S R)
; lattice_id_ann_certs := P2C_bounded S (A_eqv_eq S (A_lattice_eqv S R)) 
                                   (A_lattice_join S R) 
                                   (A_lattice_meet S R) 
                                   (A_lattice_id_ann_proofs S R)                                              
; lattice_certs       := P2C_lattice S (A_eqv_eq S (A_lattice_eqv S R)) 
                                   (A_lattice_join S R) 
                                   (A_lattice_meet S R) 
                                   (A_lattice_proofs S R)
; lattice_ast        := A_lattice_ast S R
|}.


Definition P2C_distributive_lattice : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
    distributive_lattice_proofs S r b1 b2 -> @distributive_lattice_certificates S 
:= λ S r b1 b2 p,
{|

  distributive_lattice_absorptive             := Assert_Left_Left_Absorptive
; distributive_lattice_absorptive_dual        := Assert_Left_Left_Absorptive_Dual 
; distributive_lattice_distributive           := Assert_Left_Distributive
|}. 

Definition A2C_distributive_lattice : ∀ (S : Type), A_distributive_lattice S -> @distributive_lattice S 
:= λ S R,
{|
  distributive_lattice_eqv         := A2C_eqv S (A_distributive_lattice_eqv S R)
; distributive_lattice_join        := A_distributive_lattice_join S R 
; distributive_lattice_meet        := A_distributive_lattice_meet S R 
; distributive_lattice_join_certs  := P2C_sg_CI S (A_eqv_eq S (A_distributive_lattice_eqv S R)) 
                                (A_distributive_lattice_join S R) 
                                (A_distributive_lattice_join_proofs S R)
; distributive_lattice_meet_certs := P2C_sg_CI S (A_eqv_eq S (A_distributive_lattice_eqv S R)) 
                                (A_distributive_lattice_meet S R) 
                                (A_distributive_lattice_meet_proofs S R)
; distributive_lattice_id_ann_certs := P2C_bounded S (A_eqv_eq S (A_distributive_lattice_eqv S R)) 
                                   (A_distributive_lattice_join S R) 
                                   (A_distributive_lattice_meet S R) 
                                   (A_distributive_lattice_id_ann_proofs S R)         
; distributive_lattice_certs       := P2C_distributive_lattice S 
                                        (A_eqv_eq S (A_distributive_lattice_eqv S R)) 
                                        (A_distributive_lattice_join S R)
                                        (A_distributive_lattice_meet S R)                   
                                        (A_distributive_lattice_proofs S R)
; distributive_lattice_ast        := A_distributive_lattice_ast S R
|}.



Definition A2C_selective_distributive_lattice : ∀ (S : Type), A_selective_distributive_lattice S -> @selective_distributive_lattice S 
:= λ S R,
{|
  selective_distributive_lattice_eqv         := A2C_eqv S (A_selective_distributive_lattice_eqv S R)
; selective_distributive_lattice_join        := A_selective_distributive_lattice_join S R 
; selective_distributive_lattice_meet        := A_selective_distributive_lattice_meet S R 
; selective_distributive_lattice_join_certs  := P2C_sg_CS S (A_eqv_eq S (A_selective_distributive_lattice_eqv S R)) 
                                (A_selective_distributive_lattice_join S R) 
                                (A_selective_distributive_lattice_join_proofs S R)
; selective_distributive_lattice_meet_certs := P2C_sg_CS S (A_eqv_eq S (A_selective_distributive_lattice_eqv S R)) 
                                (A_selective_distributive_lattice_meet S R) 
                                (A_selective_distributive_lattice_meet_proofs S R)
; selective_distributive_lattice_id_ann_certs := P2C_bounded S (A_eqv_eq S (A_selective_distributive_lattice_eqv S R)) 
                                   (A_selective_distributive_lattice_join S R) 
                                   (A_selective_distributive_lattice_meet S R) 
                                   (A_selective_distributive_lattice_id_ann_proofs S R)         

; selective_distributive_lattice_certs       := P2C_distributive_lattice S 
                                        (A_eqv_eq S (A_selective_distributive_lattice_eqv S R)) 
                                        (A_selective_distributive_lattice_join S R)
                                        (A_selective_distributive_lattice_meet S R)                   
                                        (A_selective_distributive_lattice_proofs S R)
; selective_distributive_lattice_ast        := A_selective_distributive_lattice_ast S R
|}.



Definition A2C_selective_distributive_prelattice : ∀ (S : Type), A_selective_distributive_prelattice S -> @selective_distributive_prelattice S 
:= λ S R,
{|
  selective_distributive_prelattice_eqv         := A2C_eqv S (A_selective_distributive_prelattice_eqv S R)
; selective_distributive_prelattice_join        := A_selective_distributive_prelattice_join S R 
; selective_distributive_prelattice_meet        := A_selective_distributive_prelattice_meet S R 
; selective_distributive_prelattice_join_certs  := P2C_sg_CS S (A_eqv_eq S (A_selective_distributive_prelattice_eqv S R)) 
                                (A_selective_distributive_prelattice_join S R) 
                                (A_selective_distributive_prelattice_join_proofs S R)
; selective_distributive_prelattice_meet_certs := P2C_sg_CS S (A_eqv_eq S (A_selective_distributive_prelattice_eqv S R)) 
                                (A_selective_distributive_prelattice_meet S R) 
                                (A_selective_distributive_prelattice_meet_proofs S R)
; selective_distributive_prelattice_id_ann_certs := P2C_id_ann S (A_eqv_eq S (A_selective_distributive_prelattice_eqv S R)) 
                                   (A_selective_distributive_prelattice_join S R) 
                                   (A_selective_distributive_prelattice_meet S R) 
                                   (A_selective_distributive_prelattice_id_ann_proofs S R)         

; selective_distributive_prelattice_certs       := P2C_distributive_lattice S 
                                        (A_eqv_eq S (A_selective_distributive_prelattice_eqv S R)) 
                                        (A_selective_distributive_prelattice_join S R)
                                        (A_selective_distributive_prelattice_meet S R)                   
                                        (A_selective_distributive_prelattice_proofs S R)
; selective_distributive_prelattice_ast        := A_selective_distributive_prelattice_ast S R
|}.



Definition A2C_distributive_prelattice : ∀ (S : Type), A_distributive_prelattice S -> @distributive_prelattice S 
:= λ S R,
{|
  distributive_prelattice_eqv         := A2C_eqv S (A_distributive_prelattice_eqv S R)
; distributive_prelattice_join        := A_distributive_prelattice_join S R 
; distributive_prelattice_meet        := A_distributive_prelattice_meet S R 
; distributive_prelattice_join_certs  := P2C_sg_CI S (A_eqv_eq S (A_distributive_prelattice_eqv S R)) 
                                (A_distributive_prelattice_join S R) 
                                (A_distributive_prelattice_join_proofs S R)
; distributive_prelattice_meet_certs := P2C_sg_CI S (A_eqv_eq S (A_distributive_prelattice_eqv S R)) 
                                (A_distributive_prelattice_meet S R) 
                                (A_distributive_prelattice_meet_proofs S R)
; distributive_prelattice_id_ann_certs := P2C_id_ann S (A_eqv_eq S (A_distributive_prelattice_eqv S R)) 
                                   (A_distributive_prelattice_join S R) 
                                   (A_distributive_prelattice_meet S R) 
                                   (A_distributive_prelattice_id_ann_proofs S R)         
; distributive_prelattice_certs       := P2C_distributive_lattice S 
                                        (A_eqv_eq S (A_distributive_prelattice_eqv S R)) 
                                        (A_distributive_prelattice_join S R)
                                        (A_distributive_prelattice_meet S R)                   
                                        (A_distributive_prelattice_proofs S R)
; distributive_prelattice_ast        := A_distributive_prelattice_ast S R
|}.



Definition P2C_path_algebra (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) (P : path_algebra_proofs S eq plus times) := 
{|
  path_algebra_left_distributive      := @Assert_Left_Distributive S
; path_algebra_right_distributive     := @Assert_Right_Distributive S
; path_algebra_left_left_absorptive   := @Assert_Left_Left_Absorptive S
; path_algebra_left_right_absorptive  := @Assert_Left_Right_Absorptive S
|}.

Definition P2C_with_one (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) (P : with_one_proofs S eq plus times) := 
{|
  with_one_exists_plus_id_d          := p2c_exists_id_check S _ _ (A_with_one_exists_plus_id_d S eq plus times P)
; with_one_exists_plus_ann           := p2c_exists_ann_assert S _ _ (A_with_one_exists_plus_ann S eq plus times P)
; with_one_exists_times_id           := p2c_exists_id_assert S _ _ (A_with_one_exists_times_id S eq plus times P)
; with_one_exists_times_ann_d        := p2c_exists_ann_check S _ _ (A_with_one_exists_times_ann_d S eq plus times P)
; with_one_plus_id_is_times_ann_d    := p2c_plus_id_equals_times_ann S _ _ _ (A_with_one_plus_id_is_times_ann_d S eq plus times P)
; with_one_times_id_is_plus_ann      := p2c_times_id_equals_plus_ann_assert S _ _ _ (A_with_one_times_id_is_plus_ann S eq plus times P)
|}.


Definition A2C_pre_path_algebra (S : Type) (P : A_pre_path_algebra S) := 
{|
  pre_path_algebra_eqv           := A2C_eqv S (A_pre_path_algebra_eqv S P)
; pre_path_algebra_plus          := A_pre_path_algebra_plus S P 
; pre_path_algebra_times         := A_pre_path_algebra_times S P 
; pre_path_algebra_plus_certs   := P2C_sg_CI S _ _ (A_pre_path_algebra_plus_proofs S P)
; pre_path_algebra_times_certs  := P2C_msg S _ _  (A_pre_path_algebra_times_proofs S P) 
; pre_path_algebra_id_ann_certs := P2C_id_ann S _ _ _ (A_pre_path_algebra_id_ann_proofs S P) 
; pre_path_algebra_certs        := P2C_path_algebra S _ _ _ (A_pre_path_algebra_proofs S P) 
; pre_path_algebra_ast           := A_pre_path_algebra_ast S P
|}.


Definition A2C_pre_path_algebra_NS (S : Type) (P : A_pre_path_algebra_NS S) := 
{|
  pre_path_algebra_NS_eqv           := A2C_eqv S (A_pre_path_algebra_NS_eqv S P)
; pre_path_algebra_NS_plus          := A_pre_path_algebra_NS_plus S P 
; pre_path_algebra_NS_times         := A_pre_path_algebra_NS_times S P 
; pre_path_algebra_NS_plus_certs   := P2C_sg_CINS S _ _ (A_pre_path_algebra_NS_plus_proofs S P)
; pre_path_algebra_NS_times_certs  := P2C_msg S _ _  (A_pre_path_algebra_NS_times_proofs S P) 
; pre_path_algebra_NS_id_ann_certs := P2C_id_ann S _ _ _ (A_pre_path_algebra_NS_id_ann_proofs S P) 
; pre_path_algebra_NS_certs        := P2C_path_algebra S _ _ _ (A_pre_path_algebra_NS_proofs S P) 
; pre_path_algebra_NS_ast           := A_pre_path_algebra_NS_ast S P
|}.

Definition A2C_pre_path_algebra_with_one (S : Type) (P : A_pre_path_algebra_with_one S) := 
{|
  pre_path_algebra_with_one_eqv           := A2C_eqv S (A_pre_path_algebra_with_one_eqv S P)
; pre_path_algebra_with_one_plus          := A_pre_path_algebra_with_one_plus S P 
; pre_path_algebra_with_one_times         := A_pre_path_algebra_with_one_times S P 
; pre_path_algebra_with_one_plus_certs   := P2C_sg_CINS S _ _ (A_pre_path_algebra_with_one_plus_proofs S P)
; pre_path_algebra_with_one_times_certs  := P2C_msg S _ _  (A_pre_path_algebra_with_one_times_proofs S P) 
; pre_path_algebra_with_one_id_ann_certs := P2C_with_one S _ _ _ (A_pre_path_algebra_with_one_id_ann_proofs S P) 
; pre_path_algebra_with_one_certs        := P2C_path_algebra S _ _ _ (A_pre_path_algebra_with_one_proofs S P) 
; pre_path_algebra_with_one_ast           := A_pre_path_algebra_with_one_ast S P
|}.





End Translation. 