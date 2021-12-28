Require Import Coq.Strings.String.
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
  A_id_ann_plus_times_d       : exists_id_ann_decidable S eq plus times (* 5 possibilities *)
; A_id_ann_times_plus_d       : exists_id_ann_decidable S eq times plus (* 5 possibilities *)                                                        
}.

Record dually_bounded_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_bounded_plus_id_is_times_ann : bops_exists_id_ann_equal S eq plus times 
; A_bounded_times_id_is_plus_ann : bops_exists_id_ann_equal S eq times plus 
}.

(* minimal requirement for semiring: plus id = times ann *)
Record pid_is_tann_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_pid_is_tann_plus_times   : bops_exists_id_ann_equal S eq plus times 
; A_pid_is_tann_times_plus_d : exists_id_ann_decidable S eq times plus                                                         
}.

(* used in A_pre_dioid_with_one *)
Record pann_is_tid_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_pann_is_tid_plus_times_d   : exists_id_ann_decidable S eq plus times 
; A_pann_is_tid_times_plus     : bops_exists_id_ann_equal S eq times plus                                                         
}.


(* if plus is always commutative, then we only need two versions of absorption *) 
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

Record dioid_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_dioid_left_distributive      : bop_left_distributive S eq plus times 
; A_dioid_right_distributive     : bop_right_distributive S eq plus times 
; A_dioid_left_left_absorptive   : bops_left_left_absorptive S eq plus times 
; A_dioid_left_right_absorptive  : bops_left_right_absorptive S eq plus times 
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
  A_bs_eqv           : A_eqv S 
; A_bs_plus          : binary_op S 
; A_bs_times         : binary_op S 
; A_bs_plus_proofs   : asg_proofs S (A_eqv_eq S A_bs_eqv) A_bs_plus    (* should we generalize to sg_proofs? note: asg is commutative! *) 
; A_bs_times_proofs  : msg_proofs S (A_eqv_eq S A_bs_eqv) A_bs_times   (* should we generalize to sg_proofs? *) 
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

Record A_semiring (S : Type) := {
  A_semiring_eqv           : A_eqv S 
; A_semiring_plus          : binary_op S 
; A_semiring_times         : binary_op S 
; A_semiring_plus_proofs   : sg_C_proofs S (A_eqv_eq S A_semiring_eqv) A_semiring_plus
; A_semiring_times_proofs  : msg_proofs S   (A_eqv_eq S A_semiring_eqv) A_semiring_times
; A_semiring_id_ann_proofs : pid_is_tann_proofs S (A_eqv_eq S A_semiring_eqv) A_semiring_plus A_semiring_times
; A_semiring_proofs        : semiring_proofs S (A_eqv_eq S A_semiring_eqv) A_semiring_plus A_semiring_times
; A_semiring_ast           : cas_ast
}.

Record A_pre_dioid (S : Type) := {
  A_pre_dioid_eqv           : A_eqv S 
; A_pre_dioid_plus          : binary_op S 
; A_pre_dioid_times         : binary_op S 
; A_pre_dioid_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_pre_dioid_eqv) A_pre_dioid_plus
; A_pre_dioid_times_proofs  : msg_proofs S   (A_eqv_eq S A_pre_dioid_eqv) A_pre_dioid_times
; A_pre_dioid_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_pre_dioid_eqv) A_pre_dioid_plus A_pre_dioid_times
; A_pre_dioid_proofs        : dioid_proofs S (A_eqv_eq S A_pre_dioid_eqv) A_pre_dioid_plus A_pre_dioid_times
; A_pre_dioid_ast           : cas_ast
}.

Record A_pre_dioid_with_one (S : Type) := {
  A_pre_dioid_with_one_eqv           : A_eqv S 
; A_pre_dioid_with_one_plus          : binary_op S 
; A_pre_dioid_with_one_times         : binary_op S 
; A_pre_dioid_with_one_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_pre_dioid_with_one_eqv) A_pre_dioid_with_one_plus
; A_pre_dioid_with_one_times_proofs  : msg_proofs S   (A_eqv_eq S A_pre_dioid_with_one_eqv) A_pre_dioid_with_one_times
; A_pre_dioid_with_one_id_ann_proofs : pann_is_tid_proofs S (A_eqv_eq S A_pre_dioid_with_one_eqv) A_pre_dioid_with_one_plus A_pre_dioid_with_one_times
; A_pre_dioid_with_one_proofs        : dioid_proofs S (A_eqv_eq S A_pre_dioid_with_one_eqv) A_pre_dioid_with_one_plus A_pre_dioid_with_one_times
; A_pre_dioid_with_one_ast           : cas_ast
}.


Record A_pre_dioid_with_zero (S : Type) := {
  A_pre_dioid_with_zero_eqv           : A_eqv S 
; A_pre_dioid_with_zero_plus          : binary_op S 
; A_pre_dioid_with_zero_times         : binary_op S 
; A_pre_dioid_with_zero_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_pre_dioid_with_zero_eqv) A_pre_dioid_with_zero_plus
; A_pre_dioid_with_zero_times_proofs  : msg_proofs S   (A_eqv_eq S A_pre_dioid_with_zero_eqv) A_pre_dioid_with_zero_times
; A_pre_dioid_with_zero_id_ann_proofs : pid_is_tann_proofs S (A_eqv_eq S A_pre_dioid_with_zero_eqv) A_pre_dioid_with_zero_plus A_pre_dioid_with_zero_times
; A_pre_dioid_with_zero_proofs        : dioid_proofs S (A_eqv_eq S A_pre_dioid_with_zero_eqv) A_pre_dioid_with_zero_plus A_pre_dioid_with_zero_times
; A_pre_dioid_with_zero_ast           : cas_ast
}.


Record A_dioid (S : Type) := {
  A_dioid_eqv           : A_eqv S 
; A_dioid_plus          : binary_op S 
; A_dioid_times         : binary_op S 
; A_dioid_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus
; A_dioid_times_proofs  : msg_proofs S   (A_eqv_eq S A_dioid_eqv) A_dioid_times
; A_dioid_id_ann_proofs : dually_bounded_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus A_dioid_times
; A_dioid_proofs        : dioid_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus A_dioid_times
; A_dioid_ast           : cas_ast
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


Record A_lattice (S : Type) := {
  A_lattice_eqv           : A_eqv S 
; A_lattice_join          : binary_op S 
; A_lattice_meet          : binary_op S 
; A_lattice_join_proofs   : sg_CI_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_join
; A_lattice_meet_proofs   : sg_CI_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_meet
; A_lattice_id_ann_proofs : dually_bounded_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_join A_lattice_meet      
; A_lattice_proofs        : lattice_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_join A_lattice_meet
; A_lattice_ast           : cas_ast
}.

Record A_distributive_lattice (S : Type) := {
  A_distributive_lattice_eqv         : A_eqv S 
; A_distributive_lattice_join        : binary_op S 
; A_distributive_lattice_meet        : binary_op S 
; A_distributive_lattice_join_proofs : sg_CI_proofs S (A_eqv_eq S A_distributive_lattice_eqv) A_distributive_lattice_join
; A_distributive_lattice_meet_proofs : sg_CI_proofs S (A_eqv_eq S A_distributive_lattice_eqv) A_distributive_lattice_meet
; A_distributive_lattice_id_ann_proofs : dually_bounded_proofs S
                                          (A_eqv_eq S A_distributive_lattice_eqv)
                                          A_distributive_lattice_join
                                          A_distributive_lattice_meet                                                        
; A_distributive_lattice_proofs      : distributive_lattice_proofs S
                                          (A_eqv_eq S A_distributive_lattice_eqv)
                                          A_distributive_lattice_join
                                          A_distributive_lattice_meet
; A_distributive_lattice_ast         : cas_ast
}.

(*************** structures with a selective additive operation ********************)

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

Record A_selective_semiring (S : Type) := {
  A_selective_semiring_eqv           : A_eqv S 
; A_selective_semiring_plus          : binary_op S 
; A_selective_semiring_times         : binary_op S 
; A_selective_semiring_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_plus
; A_selective_semiring_times_proofs  : msg_proofs S   (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_times
; A_selective_semiring_id_ann_proofs : pid_is_tann_proofs S (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_plus A_selective_semiring_times
; A_selective_semiring_proofs        : semiring_proofs S (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_plus A_selective_semiring_times
; A_selective_semiring_ast           : cas_ast
}.

Record A_selective_pre_dioid (S : Type) := {
  A_selective_pre_dioid_eqv           : A_eqv S 
; A_selective_pre_dioid_plus          : binary_op S 
; A_selective_pre_dioid_times         : binary_op S 
; A_selective_pre_dioid_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_pre_dioid_eqv) A_selective_pre_dioid_plus
; A_selective_pre_dioid_times_proofs  : msg_proofs S   (A_eqv_eq S A_selective_pre_dioid_eqv) A_selective_pre_dioid_times
; A_selective_pre_dioid_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_selective_pre_dioid_eqv) A_selective_pre_dioid_plus A_selective_pre_dioid_times
; A_selective_pre_dioid_proofs        : dioid_proofs S (A_eqv_eq S A_selective_pre_dioid_eqv) A_selective_pre_dioid_plus A_selective_pre_dioid_times
; A_selective_pre_dioid_ast           : cas_ast
}.

Record A_selective_pre_dioid_with_zero (S : Type) := {
  A_selective_pre_dioid_with_zero_eqv           : A_eqv S 
; A_selective_pre_dioid_with_zero_plus          : binary_op S 
; A_selective_pre_dioid_with_zero_times         : binary_op S 
; A_selective_pre_dioid_with_zero_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_pre_dioid_with_zero_eqv) A_selective_pre_dioid_with_zero_plus
; A_selective_pre_dioid_with_zero_times_proofs  : msg_proofs S   (A_eqv_eq S A_selective_pre_dioid_with_zero_eqv) A_selective_pre_dioid_with_zero_times
; A_selective_pre_dioid_with_zero_id_ann_proofs : pid_is_tann_proofs S (A_eqv_eq S A_selective_pre_dioid_with_zero_eqv) A_selective_pre_dioid_with_zero_plus A_selective_pre_dioid_with_zero_times
; A_selective_pre_dioid_with_zero_proofs        : dioid_proofs S (A_eqv_eq S A_selective_pre_dioid_with_zero_eqv) A_selective_pre_dioid_with_zero_plus A_selective_pre_dioid_with_zero_times
; A_selective_pre_dioid_with_zero_ast           : cas_ast
}.

Record A_selective_pre_dioid_with_one (S : Type) := {
  A_selective_pre_dioid_with_one_eqv           : A_eqv S 
; A_selective_pre_dioid_with_one_plus          : binary_op S 
; A_selective_pre_dioid_with_one_times         : binary_op S 
; A_selective_pre_dioid_with_one_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_pre_dioid_with_one_eqv) A_selective_pre_dioid_with_one_plus
; A_selective_pre_dioid_with_one_times_proofs  : msg_proofs S   (A_eqv_eq S A_selective_pre_dioid_with_one_eqv) A_selective_pre_dioid_with_one_times
; A_selective_pre_dioid_with_one_id_ann_proofs : pann_is_tid_proofs S (A_eqv_eq S A_selective_pre_dioid_with_one_eqv) A_selective_pre_dioid_with_one_plus A_selective_pre_dioid_with_one_times
; A_selective_pre_dioid_with_one_proofs        : dioid_proofs S (A_eqv_eq S A_selective_pre_dioid_with_one_eqv) A_selective_pre_dioid_with_one_plus A_selective_pre_dioid_with_one_times
; A_selective_pre_dioid_with_one_ast           : cas_ast
}.

Record A_selective_dioid (S : Type) := {
  A_selective_dioid_eqv           : A_eqv S 
; A_selective_dioid_plus          : binary_op S 
; A_selective_dioid_times         : binary_op S 
; A_selective_dioid_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_plus
; A_selective_dioid_times_proofs  : msg_proofs S   (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_times
; A_selective_dioid_id_ann_proofs : dually_bounded_proofs S (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_plus A_selective_dioid_times
; A_selective_dioid_proofs        : dioid_proofs S (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_plus A_selective_dioid_times
; A_selective_dioid_ast           : cas_ast
}.







Record A_selective_cancellative_pre_dioid (S : Type) := {
  A_selective_cancellative_pre_dioid_eqv           : A_eqv S 
; A_selective_cancellative_pre_dioid_plus          : binary_op S 
; A_selective_cancellative_pre_dioid_times         : binary_op S 
; A_selective_cancellative_pre_dioid_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_eqv) A_selective_cancellative_pre_dioid_plus
; A_selective_cancellative_pre_dioid_times_proofs  : sg_CK_proofs S   (A_eqv_eq S A_selective_cancellative_pre_dioid_eqv) A_selective_cancellative_pre_dioid_times
; A_selective_cancellative_pre_dioid_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_eqv) A_selective_cancellative_pre_dioid_plus A_selective_cancellative_pre_dioid_times
; A_selective_cancellative_pre_dioid_proofs        : dioid_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_eqv) A_selective_cancellative_pre_dioid_plus A_selective_cancellative_pre_dioid_times
; A_selective_cancellative_pre_dioid_ast           : cas_ast
}.

Record A_selective_cancellative_pre_dioid_with_zero (S : Type) := {
  A_selective_cancellative_pre_dioid_with_zero_eqv           : A_eqv S 
; A_selective_cancellative_pre_dioid_with_zero_plus          : binary_op S 
; A_selective_cancellative_pre_dioid_with_zero_times         : binary_op S 
; A_selective_cancellative_pre_dioid_with_zero_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_with_zero_eqv) A_selective_cancellative_pre_dioid_with_zero_plus
; A_selective_cancellative_pre_dioid_with_zero_times_proofs  : sg_CK_proofs S   (A_eqv_eq S A_selective_cancellative_pre_dioid_with_zero_eqv) A_selective_cancellative_pre_dioid_with_zero_times
; A_selective_cancellative_pre_dioid_with_zero_id_ann_proofs : pid_is_tann_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_with_zero_eqv) A_selective_cancellative_pre_dioid_with_zero_plus A_selective_cancellative_pre_dioid_with_zero_times
; A_selective_cancellative_pre_dioid_with_zero_proofs        : dioid_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_with_zero_eqv) A_selective_cancellative_pre_dioid_with_zero_plus A_selective_cancellative_pre_dioid_with_zero_times
; A_selective_cancellative_pre_dioid_with_zero_ast           : cas_ast
}.

Record A_selective_cancellative_pre_dioid_with_one (S : Type) := {
  A_selective_cancellative_pre_dioid_with_one_eqv           : A_eqv S 
; A_selective_cancellative_pre_dioid_with_one_plus          : binary_op S 
; A_selective_cancellative_pre_dioid_with_one_times         : binary_op S 
; A_selective_cancellative_pre_dioid_with_one_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_with_one_eqv) A_selective_cancellative_pre_dioid_with_one_plus
; A_selective_cancellative_pre_dioid_with_one_times_proofs  : sg_CK_proofs S   (A_eqv_eq S A_selective_cancellative_pre_dioid_with_one_eqv) A_selective_cancellative_pre_dioid_with_one_times
; A_selective_cancellative_pre_dioid_with_one_id_ann_proofs : pann_is_tid_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_with_one_eqv) A_selective_cancellative_pre_dioid_with_one_plus A_selective_cancellative_pre_dioid_with_one_times
; A_selective_cancellative_pre_dioid_with_one_proofs        : dioid_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_with_one_eqv) A_selective_cancellative_pre_dioid_with_one_plus A_selective_cancellative_pre_dioid_with_one_times
; A_selective_cancellative_pre_dioid_with_one_ast           : cas_ast
}.

Record A_selective_cancellative_dioid (S : Type) := {
  A_selective_cancellative_dioid_eqv           : A_eqv S 
; A_selective_cancellative_dioid_plus          : binary_op S 
; A_selective_cancellative_dioid_times         : binary_op S 
; A_selective_cancellative_dioid_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_cancellative_dioid_eqv) A_selective_cancellative_dioid_plus
; A_selective_cancellative_dioid_times_proofs  : sg_CK_proofs S   (A_eqv_eq S A_selective_cancellative_dioid_eqv) A_selective_cancellative_dioid_times
; A_selective_cancellative_dioid_id_ann_proofs : dually_bounded_proofs S (A_eqv_eq S A_selective_cancellative_dioid_eqv) A_selective_cancellative_dioid_plus A_selective_cancellative_dioid_times
; A_selective_cancellative_dioid_proofs        : dioid_proofs S (A_eqv_eq S A_selective_cancellative_dioid_eqv) A_selective_cancellative_dioid_plus A_selective_cancellative_dioid_times
; A_selective_cancellative_dioid_ast           : cas_ast
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

Record A_selective_distributive_prelattice_with_zero (S : Type) := {
  A_selective_distributive_prelattice_with_zero_eqv         : A_eqv S 
; A_selective_distributive_prelattice_with_zero_join        : binary_op S 
; A_selective_distributive_prelattice_with_zero_meet        : binary_op S 
; A_selective_distributive_prelattice_with_zero_join_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_prelattice_with_zero_eqv) A_selective_distributive_prelattice_with_zero_join
; A_selective_distributive_prelattice_with_zero_meet_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_prelattice_with_zero_eqv) A_selective_distributive_prelattice_with_zero_meet
; A_selective_distributive_prelattice_with_zero_id_ann_proofs : pid_is_tann_proofs S
                                          (A_eqv_eq S A_selective_distributive_prelattice_with_zero_eqv)
                                          A_selective_distributive_prelattice_with_zero_join
                                          A_selective_distributive_prelattice_with_zero_meet                                                                  
; A_selective_distributive_prelattice_with_zero_proofs      : distributive_lattice_proofs S
                                          (A_eqv_eq S A_selective_distributive_prelattice_with_zero_eqv)
                                          A_selective_distributive_prelattice_with_zero_join
                                          A_selective_distributive_prelattice_with_zero_meet
; A_selective_distributive_prelattice_with_zero_ast         : cas_ast
}.


Record A_selective_distributive_prelattice_with_one (S : Type) := {
  A_selective_distributive_prelattice_with_one_eqv         : A_eqv S 
; A_selective_distributive_prelattice_with_one_join        : binary_op S 
; A_selective_distributive_prelattice_with_one_meet        : binary_op S 
; A_selective_distributive_prelattice_with_one_join_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_prelattice_with_one_eqv) A_selective_distributive_prelattice_with_one_join
; A_selective_distributive_prelattice_with_one_meet_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_prelattice_with_one_eqv) A_selective_distributive_prelattice_with_one_meet
; A_selective_distributive_prelattice_with_one_id_ann_proofs : pann_is_tid_proofs S
                                          (A_eqv_eq S A_selective_distributive_prelattice_with_one_eqv)
                                          A_selective_distributive_prelattice_with_one_join
                                          A_selective_distributive_prelattice_with_one_meet                                                                  
; A_selective_distributive_prelattice_with_one_proofs      : distributive_lattice_proofs S
                                          (A_eqv_eq S A_selective_distributive_prelattice_with_one_eqv)
                                          A_selective_distributive_prelattice_with_one_join
                                          A_selective_distributive_prelattice_with_one_meet
; A_selective_distributive_prelattice_with_one_ast         : cas_ast
}.


Record A_selective_distributive_lattice (S : Type) := {
  A_selective_distributive_lattice_eqv         : A_eqv S 
; A_selective_distributive_lattice_join        : binary_op S 
; A_selective_distributive_lattice_meet        : binary_op S 
; A_selective_distributive_lattice_join_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_lattice_eqv) A_selective_distributive_lattice_join
; A_selective_distributive_lattice_meet_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_lattice_eqv) A_selective_distributive_lattice_meet
; A_selective_distributive_lattice_id_ann_proofs : dually_bounded_proofs S
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

Section AMCAS.

Inductive A_bs_mcas S : Type :=
| A_BS_Error : string                 -> A_bs_mcas S
| A_BS_bs : A_bs S                    -> A_bs_mcas S
| A_BS_bs_CI : A_bs_CI S              -> A_bs_mcas S                                   
| A_BS_bs_CS : A_bs_CS S              -> A_bs_mcas S                                     
| A_BS_presemiring  : A_presemiring S -> A_bs_mcas S
| A_BS_semiring  : A_semiring S       -> A_bs_mcas S
| A_BS_pre_dioid  : A_pre_dioid S     -> A_bs_mcas S
| A_BS_pre_dioid_with_one  : A_pre_dioid_with_one S -> A_bs_mcas S
| A_BS_pre_dioid_with_zero  : A_pre_dioid_with_zero S -> A_bs_mcas S
| A_BS_dioid  : A_dioid S              -> A_bs_mcas S
| A_BS_prelattice  : A_prelattice S -> A_bs_mcas S
| A_BS_distributive_prelattice  : A_distributive_prelattice S -> A_bs_mcas S
| A_BS_lattice  : A_lattice S          -> A_bs_mcas S
| A_BS_distributive_lattice  : A_distributive_lattice S -> A_bs_mcas S
| A_BS_selective_presemiring  : A_selective_presemiring S -> A_bs_mcas S
| A_BS_selective_semiring  : A_selective_semiring S -> A_bs_mcas S
| A_BS_selective_pre_dioid  : A_selective_pre_dioid S -> A_bs_mcas S
| A_BS_selective_pre_dioid_with_zero  : A_selective_pre_dioid_with_zero S -> A_bs_mcas S
| A_BS_selective_pre_dioid_with_one  : A_selective_pre_dioid_with_one S -> A_bs_mcas S
| A_BS_selective_dioid  : A_selective_dioid S -> A_bs_mcas S                                                                                          
| A_BS_selective_cancellative_pre_dioid  : A_selective_cancellative_pre_dioid S -> A_bs_mcas S
| A_BS_selective_cancellative_pre_dioid_with_zero  : A_selective_cancellative_pre_dioid_with_zero S -> A_bs_mcas S
| A_BS_selective_cancellative_pre_dioid_with_one  : A_selective_cancellative_pre_dioid_with_one S -> A_bs_mcas S
| A_BS_selective_cancellative_dioid  : A_selective_cancellative_dioid S -> A_bs_mcas S
| A_BS_selective_distributive_prelattice  : A_selective_distributive_prelattice S -> A_bs_mcas S
| A_BS_selective_distributive_prelattice_with_zero  : A_selective_distributive_prelattice_with_zero S -> A_bs_mcas S    
| A_BS_selective_distributive_prelattice_with_one  : A_selective_distributive_prelattice_with_one S -> A_bs_mcas S
| A_BS_selective_distributive_lattice  : A_selective_distributive_lattice S -> A_bs_mcas S
. 

Definition A_bs_classify (S : Type) (A : A_bs S) : A_bs_mcas S :=
let ast     := A_bs_ast _ A in
let eqv     := A_bs_eqv _ A in
let plus    := A_bs_plus _ A in      
let plusP   := A_bs_plus_proofs _ A in
let passoc  := A_asg_associative _ _ _ plusP in
let pcong   := A_asg_congruence _ _ _ plusP in
let pcomm   := A_asg_commutative _ _ _ plusP in
let sel_d   := A_asg_selective_d _ _ _ plusP in
let idem_d  := A_asg_idempotent_d _ _ _ plusP in   
let id_annP := A_bs_id_ann_proofs _ A in
let pid_id_tann_d := A_id_ann_plus_times_d _ _ _ _ id_annP in
let tid_id_pann_d := A_id_ann_times_plus_d _ _ _ _ id_annP in
let times   := A_bs_times _ A in
let timesP  := A_bs_times_proofs _ A in
let comm_d  := A_msg_commutative_d _ _ _ timesP in
(*
let left_d  : = A_msg_is_left_d _ timesP in
let right_d := A_msg_is_right_d _ timesP in
*) 
let left_can_d := A_msg_left_cancel_d  _ _ _ timesP in
let right_can_d := A_msg_right_cancel_d  _ _ _ timesP in
(*
let left_con_d := A_msg_left_constant_d  _ timesP in
let right_con_d := A_msg_right_constant_d  _ timesP in
let anti_left_d := A_msg_anti_left_d  _ timesP in
let anti_right_d := A_msg_anti_right_d  _ timesP in
*) 
let P       := A_bs_proofs _ A in
let LD_d := A_bs_left_distributive_d _ _ _ _ P in 
let RD_d := A_bs_right_distributive_d _ _ _ _ P in 
let LLA_d := A_bs_left_left_absorptive_d _ _ _ _ P in 
let LRA_d := A_bs_left_right_absorptive_d _ _ _ _ P in
(* 
let RLA_d := A_bs_right_left_absorptive_d _ _ _ _ P in 
let RRA_d := A_bs_right_right_absorptive_d _ _ _ _ P in                      
*)
match sel_d with
| inl sel  =>
  (************* Selective *****************)
  let sg_cs_p := {|
                      A_sg_CS_associative    := passoc 
                    ; A_sg_CS_congruence    := pcong 
                    ; A_sg_CS_commutative   := pcomm 
                    ; A_sg_CS_selective     := sel 
                  |} in
  let bs_cs := {|
                    A_bs_CS_eqv           := eqv 
                  ; A_bs_CS_plus          := plus
                  ; A_bs_CS_times         := times 
                  ; A_bs_CS_plus_proofs   := sg_cs_p 
                  ; A_bs_CS_times_proofs  := timesP 
                  ; A_bs_CS_id_ann_proofs := id_annP 
                  ; A_bs_CS_proofs        := P 
                  ; A_bs_CS_ast           := ast 
                  |} in 
  match LD_d with
  | inl LD  =>
    match RD_d with
    | inl RD  =>
      match LLA_d, LRA_d with
      | inl LLA, inl LRA  =>
        let doid_p :=
            {|
                A_dioid_left_distributive     := LD 
              ; A_dioid_right_distributive    := RD 
              ; A_dioid_left_left_absorptive  := LLA 
              ; A_dioid_left_right_absorptive := LRA 
              |} in
        match pid_id_tann_d, tid_id_pann_d with
        | Id_Ann_Proof_Equal _ _ _ _ plus_id_is_times_ann, Id_Ann_Proof_Equal _ _ _ _ times_id_is_plus_ann =>
             A_BS_selective_dioid _
               {|
                   A_selective_dioid_eqv := eqv 
                 ; A_selective_dioid_plus := plus
                 ; A_selective_dioid_times := times 
                 ; A_selective_dioid_plus_proofs := sg_cs_p 
                 ; A_selective_dioid_times_proofs := timesP  
                 ; A_selective_dioid_id_ann_proofs :=
                     {|
                         A_bounded_plus_id_is_times_ann := plus_id_is_times_ann
                       ; A_bounded_times_id_is_plus_ann := times_id_is_plus_ann                      
                     |} 
                 ; A_selective_dioid_proofs := doid_p 
                 ; A_selective_dioid_ast := ast 
               |} 
        | _ , Id_Ann_Proof_Equal _ _ _ _ times_id_is_plus_ann =>
              A_BS_selective_pre_dioid_with_one _
                {|
                   A_selective_pre_dioid_with_one_eqv := eqv 
                 ; A_selective_pre_dioid_with_one_plus := plus
                 ; A_selective_pre_dioid_with_one_times := times 
                 ; A_selective_pre_dioid_with_one_plus_proofs := sg_cs_p 
                 ; A_selective_pre_dioid_with_one_times_proofs := timesP  
                 ; A_selective_pre_dioid_with_one_id_ann_proofs :=
                     {|
                         A_pann_is_tid_plus_times_d  := pid_id_tann_d
                       ; A_pann_is_tid_times_plus  := times_id_is_plus_ann                                             
                     |} 
                 ; A_selective_pre_dioid_with_one_proofs := doid_p 
                 ; A_selective_pre_dioid_with_one_ast := ast 
                |} 
        | Id_Ann_Proof_Equal _ _ _ _ plus_id_is_times_ann, _ =>
             A_BS_selective_pre_dioid_with_zero _
                {|
                   A_selective_pre_dioid_with_zero_eqv := eqv 
                 ; A_selective_pre_dioid_with_zero_plus := plus
                 ; A_selective_pre_dioid_with_zero_times := times 
                 ; A_selective_pre_dioid_with_zero_plus_proofs := sg_cs_p 
                 ; A_selective_pre_dioid_with_zero_times_proofs := timesP  
                 ; A_selective_pre_dioid_with_zero_id_ann_proofs :=
                     {|
                         A_pid_is_tann_plus_times   := plus_id_is_times_ann
                       ; A_pid_is_tann_times_plus_d := tid_id_pann_d                     
                     |} 
                 ; A_selective_pre_dioid_with_zero_proofs := doid_p 
                 ; A_selective_pre_dioid_with_zero_ast := ast 
                |} 
        | _, _ => A_BS_selective_pre_dioid _
               {|
                   A_selective_pre_dioid_eqv := eqv 
                 ; A_selective_pre_dioid_plus := plus
                 ; A_selective_pre_dioid_times := times 
                 ; A_selective_pre_dioid_plus_proofs := sg_cs_p 
                 ; A_selective_pre_dioid_times_proofs := timesP  
                 ; A_selective_pre_dioid_id_ann_proofs := id_annP
                 ; A_selective_pre_dioid_proofs := doid_p 
                 ; A_selective_pre_dioid_ast := ast 
               |} 
        end
      | _, _ => A_BS_bs_CS _ bs_cs  (* selective semiring? *) 
      end 
    | inr nRD => A_BS_bs_CS _ bs_cs
    end 
  | inr nLD => A_BS_bs_CS _ bs_cs
  end 
| inr nsel =>
  match idem_d with
  | inl idem =>
    (************* Idempotent, Not Selective *****************)
    let sg_ci_p := {|
                     A_sg_CI_associative    := passoc 
                    ; A_sg_CI_congruence    := pcong 
                    ; A_sg_CI_commutative   := pcomm 
                    ; A_sg_CI_idempotent    := idem 
                    ; A_sg_CI_not_selective := nsel 
                  |} in
    let bs_ci := {|
                    A_bs_CI_eqv           := eqv 
                  ; A_bs_CI_plus          := plus
                  ; A_bs_CI_times         := times 
                  ; A_bs_CI_plus_proofs   := sg_ci_p 
                  ; A_bs_CI_times_proofs  := timesP 
                  ; A_bs_CI_id_ann_proofs := id_annP 
                  ; A_bs_CI_proofs        := P 
                  ; A_bs_CI_ast           := ast 
                  |} in 
    match LD_d with
    | inl LD =>
      match RD_d with
      | inl RD =>
        match LLA_d with
        | inl LLA  =>
          match LRA_d with
          | inl LRA  =>
            let doid_p := {|
                            A_dioid_left_distributive     := LD 
                           ; A_dioid_right_distributive    := RD 
                           ; A_dioid_left_left_absorptive  := LLA 
                           ; A_dioid_left_right_absorptive := LRA 
                |} in
            match pid_id_tann_d, tid_id_pann_d with
            | Id_Ann_Proof_Equal _ _ _ _ plus_id_is_times_ann, Id_Ann_Proof_Equal _ _ _ _ times_id_is_plus_ann =>
              A_BS_dioid _ {|
                             A_dioid_eqv := eqv 
                           ; A_dioid_plus := plus
                           ; A_dioid_times := times 
                           ; A_dioid_plus_proofs := sg_ci_p 
                           ; A_dioid_times_proofs := timesP  
                           ; A_dioid_id_ann_proofs :=
                               {|
                                   A_bounded_plus_id_is_times_ann := plus_id_is_times_ann
                                 ; A_bounded_times_id_is_plus_ann := times_id_is_plus_ann                      
                               |} 
                           ; A_dioid_proofs := doid_p 
                           ; A_dioid_ast := ast 
                           |} 
            | _ , Id_Ann_Proof_Equal _ _ _ _ times_id_is_plus_ann =>
              A_BS_pre_dioid_with_one _ {|
                                        A_pre_dioid_with_one_eqv := eqv 
                                        ; A_pre_dioid_with_one_plus := plus
                                        ; A_pre_dioid_with_one_times := times 
                                        ; A_pre_dioid_with_one_plus_proofs := sg_ci_p 
                                        ; A_pre_dioid_with_one_times_proofs := timesP  
                                        ; A_pre_dioid_with_one_id_ann_proofs :=
                                            {|
                                                A_pann_is_tid_plus_times_d  := pid_id_tann_d
                                              ; A_pann_is_tid_times_plus := times_id_is_plus_ann                                             
                                            |} 
                                        ; A_pre_dioid_with_one_proofs := doid_p 
                                        ; A_pre_dioid_with_one_ast := ast 
                           |} 
            | Id_Ann_Proof_Equal _ _ _ _ plus_id_is_times_ann, _ =>
              A_BS_pre_dioid_with_zero _ {|
                                         A_pre_dioid_with_zero_eqv := eqv 
                                         ; A_pre_dioid_with_zero_plus := plus
                                         ; A_pre_dioid_with_zero_times := times 
                                         ; A_pre_dioid_with_zero_plus_proofs := sg_ci_p 
                                         ; A_pre_dioid_with_zero_times_proofs := timesP  
                                         ; A_pre_dioid_with_zero_id_ann_proofs :=
                                             {|
                                               A_pid_is_tann_plus_times   := plus_id_is_times_ann
                                              ; A_pid_is_tann_times_plus_d := tid_id_pann_d                     
                                             |} 
                                         ; A_pre_dioid_with_zero_proofs := doid_p 
                                         ; A_pre_dioid_with_zero_ast := ast 
                           |} 
            | _, _ => A_BS_pre_dioid _ {|
                                       A_pre_dioid_eqv := eqv 
                                       ; A_pre_dioid_plus := plus
                                       ; A_pre_dioid_times := times 
                                       ; A_pre_dioid_plus_proofs := sg_ci_p 
                                       ; A_pre_dioid_times_proofs := timesP  
                                       ; A_pre_dioid_id_ann_proofs := id_annP
                                       ; A_pre_dioid_proofs := doid_p 
                                       ; A_pre_dioid_ast := ast                                        
                                       |} 
            end
          | inr nLRA => A_BS_bs_CI _ bs_ci
          end 
        | inr nLLA => A_BS_bs_CI _ bs_ci
        end 
      | _      => A_BS_bs_CI _ bs_ci
      end 
    |      _ => A_BS_bs_CI _ bs_ci 
    end 
  | inr nidem =>
  (************* Not Idempotent *****************)         
    match LD_d with
    | inl LD =>
      match RD_d with
      | inl RD => A_BS_bs _ A (* No, check for semiring *) 
      | _      => A_BS_bs _ A 
      end 
    |      _ => A_BS_bs _ A 
    end 
  end 
end.


End AMCAS.   

Section CAS.

Record id_ann_certificates {S: Type} := 
{
  id_ann_plus_times_d       : @exists_id_ann_certificate S
; id_ann_times_plus_d       : @exists_id_ann_certificate S
}.

Record dually_bounded_certificates {S: Type} := 
{
  bounded_plus_id_is_times_ann : @assert_exists_id_ann_equal S 
; bounded_times_id_is_plus_ann : @assert_exists_id_ann_equal S 
}.

Record pid_is_tann_certificates {S: Type} := 
{
  pid_is_tann_plus_times   : @assert_exists_id_ann_equal S 
; pid_is_tann_times_plus_d : @exists_id_ann_certificate S
}.

Record pann_is_tid_certificates {S: Type} := 
{
  pann_is_tid_plus_times_d   : @exists_id_ann_certificate S
; pann_is_tid_times_plus     : @assert_exists_id_ann_equal S 
}.



Record bs_certificates {S: Type} := 
{
  bs_left_distributive_d      : @check_left_distributive S
; bs_right_distributive_d     : @check_right_distributive S
; bs_left_left_absorptive_d   : @check_left_left_absorptive S
; bs_left_right_absorptive_d  : @check_left_right_absorptive S
; bs_right_left_absorptive_d  : @check_right_left_absorptive S
; bs_right_right_absorptive_d : @check_right_right_absorptive S
}. 

Record semiring_certificates {S: Type} := 
{
  semiring_left_distributive      : @assert_left_distributive S
; semiring_right_distributive     : @assert_right_distributive S

; semiring_left_left_absorptive_d   : @check_left_left_absorptive S
; semiring_left_right_absorptive_d  : @check_left_right_absorptive S 
}.

Record dioid_certificates {S: Type} := 
{
  dioid_left_distributive      : @assert_left_distributive S 
; dioid_right_distributive     : @assert_right_distributive S 
; dioid_left_left_absorptive   : @assert_left_left_absorptive S 
; dioid_left_right_absorptive  : @assert_left_right_absorptive S 
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
; semiring_id_ann_certs : @pid_is_tann_certificates S
; semiring_certs        : @semiring_certificates S
; semiring_ast          : cas_ast
}.

Record selective_semiring {S : Type} := {
  selective_semiring_eqv          : @eqv S 
; selective_semiring_plus         : binary_op S 
; selective_semiring_times        : binary_op S 
; selective_semiring_plus_certs   : @sg_CS_certificates S 
; selective_semiring_times_certs  : @msg_certificates S
; selective_semiring_id_ann_certs : @pid_is_tann_certificates S
; selective_semiring_certs        : @semiring_certificates S
; selective_semiring_ast          : cas_ast
}.


Record pre_dioid {S : Type} := {
  pre_dioid_eqv          : @eqv S 
; pre_dioid_plus         : @binary_op S 
; pre_dioid_times        : @binary_op S 
; pre_dioid_plus_certs   : @sg_CI_certificates S 
; pre_dioid_times_certs  : @msg_certificates S 
; pre_dioid_id_ann_certs : @id_ann_certificates S 
; pre_dioid_certs        : @dioid_certificates S 
; pre_dioid_ast          : cas_ast
}.

Record pre_dioid_with_one {S : Type} := {
  pre_dioid_with_one_eqv          : @eqv S 
; pre_dioid_with_one_plus         : @binary_op S 
; pre_dioid_with_one_times        : @binary_op S 
; pre_dioid_with_one_plus_certs   : @sg_CI_certificates S 
; pre_dioid_with_one_times_certs  : @msg_certificates S 
; pre_dioid_with_one_id_ann_certs : @pann_is_tid_certificates S 
; pre_dioid_with_one_certs        : @dioid_certificates S 
; pre_dioid_with_one_ast          : cas_ast
}.

Record pre_dioid_with_zero {S : Type} := {
  pre_dioid_with_zero_eqv          : @eqv S 
; pre_dioid_with_zero_plus         : @binary_op S 
; pre_dioid_with_zero_times        : @binary_op S 
; pre_dioid_with_zero_plus_certs   : @sg_CI_certificates S 
; pre_dioid_with_zero_times_certs  : @msg_certificates S 
; pre_dioid_with_zero_id_ann_certs : @pid_is_tann_certificates S 
; pre_dioid_with_zero_certs        : @dioid_certificates S 
; pre_dioid_with_zero_ast          : cas_ast
}.

Record dioid (S : Type) := {
  dioid_eqv           : @eqv S 
; dioid_plus          : binary_op S 
; dioid_times         : binary_op S 
; dioid_plus_certs    : @sg_CI_certificates S 
; dioid_times_certs   : @msg_certificates S 
; dioid_id_ann_certs  : @dually_bounded_certificates S 
; dioid_certs         : @dioid_certificates S 
; dioid_ast           : cas_ast
}.


Record selective_pre_dioid (S : Type) := {
  selective_pre_dioid_eqv           : @eqv S 
; selective_pre_dioid_plus          : binary_op S 
; selective_pre_dioid_times         : binary_op S 
; selective_pre_dioid_plus_certs    : @sg_CS_certificates S 
; selective_pre_dioid_times_certs   : @msg_certificates S 
; selective_pre_dioid_id_ann_certs  : @id_ann_certificates S 
; selective_pre_dioid_certs         : @dioid_certificates S 
; selective_pre_dioid_ast           : cas_ast
}.

Record selective_pre_dioid_with_one (S : Type) := {
  selective_pre_dioid_with_one_eqv           : @eqv S 
; selective_pre_dioid_with_one_plus          : binary_op S 
; selective_pre_dioid_with_one_times         : binary_op S 
; selective_pre_dioid_with_one_plus_certs    : @sg_CS_certificates S 
; selective_pre_dioid_with_one_times_certs   : @msg_certificates S 
; selective_pre_dioid_with_one_id_ann_certs  : @pann_is_tid_certificates S 
; selective_pre_dioid_with_one_certs         : @dioid_certificates S 
; selective_pre_dioid_with_one_ast           : cas_ast
}.

Record selective_pre_dioid_with_zero (S : Type) := {
  selective_pre_dioid_with_zero_eqv           : @eqv S 
; selective_pre_dioid_with_zero_plus          : binary_op S 
; selective_pre_dioid_with_zero_times         : binary_op S 
; selective_pre_dioid_with_zero_plus_certs    : @sg_CS_certificates S 
; selective_pre_dioid_with_zero_times_certs   : @msg_certificates S 
; selective_pre_dioid_with_zero_id_ann_certs  : @pid_is_tann_certificates S 
; selective_pre_dioid_with_zero_certs         : @dioid_certificates S 
; selective_pre_dioid_with_zero_ast           : cas_ast
}.


Record selective_dioid (S : Type) := {
  selective_dioid_eqv           : @eqv S 
; selective_dioid_plus          : binary_op S 
; selective_dioid_times         : binary_op S 
; selective_dioid_plus_certs    : @sg_CS_certificates S 
; selective_dioid_times_certs   : @msg_certificates S 
; selective_dioid_id_ann_certs  : @dually_bounded_certificates S 
; selective_dioid_certs         : @dioid_certificates S 
; selective_dioid_ast           : cas_ast
}.


Record selective_cancellative_pre_dioid (S : Type) := {
  selective_cancellative_pre_dioid_eqv           : @eqv S 
; selective_cancellative_pre_dioid_plus          : binary_op S 
; selective_cancellative_pre_dioid_times         : binary_op S 
; selective_cancellative_pre_dioid_plus_certs    : @sg_CS_certificates S 
; selective_cancellative_pre_dioid_times_certs   : @sg_CK_certificates S 
; selective_cancellative_pre_dioid_id_ann_certs  : @id_ann_certificates S 
; selective_cancellative_pre_dioid_certs         : @dioid_certificates S 
; selective_cancellative_pre_dioid_ast           : cas_ast
}.

Record selective_cancellative_pre_dioid_with_one (S : Type) := {
  selective_cancellative_pre_dioid_with_one_eqv           : @eqv S 
; selective_cancellative_pre_dioid_with_one_plus          : binary_op S 
; selective_cancellative_pre_dioid_with_one_times         : binary_op S 
; selective_cancellative_pre_dioid_with_one_plus_certs    : @sg_CS_certificates S 
; selective_cancellative_pre_dioid_with_one_times_certs   : @sg_CK_certificates S 
; selective_cancellative_pre_dioid_with_one_id_ann_certs  : @pann_is_tid_certificates S 
; selective_cancellative_pre_dioid_with_one_certs         : @dioid_certificates S 
; selective_cancellative_pre_dioid_with_one_ast           : cas_ast
}.

Record selective_cancellative_pre_dioid_with_zero (S : Type) := {
  selective_cancellative_pre_dioid_with_zero_eqv           : @eqv S 
; selective_cancellative_pre_dioid_with_zero_plus          : binary_op S 
; selective_cancellative_pre_dioid_with_zero_times         : binary_op S 
; selective_cancellative_pre_dioid_with_zero_plus_certs    : @sg_CS_certificates S 
; selective_cancellative_pre_dioid_with_zero_times_certs   : @sg_CK_certificates S 
; selective_cancellative_pre_dioid_with_zero_id_ann_certs  : @pid_is_tann_certificates S 
; selective_cancellative_pre_dioid_with_zero_certs         : @dioid_certificates S 
; selective_cancellative_pre_dioid_with_zero_ast           : cas_ast
}.


Record selective_cancellative_dioid (S : Type) := {
  selective_cancellative_dioid_eqv           : @eqv S 
; selective_cancellative_dioid_plus          : binary_op S 
; selective_cancellative_dioid_times         : binary_op S 
; selective_cancellative_dioid_plus_certs    : @sg_CS_certificates S 
; selective_cancellative_dioid_times_certs   : @sg_CK_certificates S 
; selective_cancellative_dioid_id_ann_certs  : @dually_bounded_certificates S 
; selective_cancellative_dioid_certs         : @dioid_certificates S 
; selective_cancellative_dioid_ast           : cas_ast
}.



Record prelattice {S : Type} := {
  prelattice_eqv           : @eqv S 
; prelattice_join          : binary_op S 
; prelattice_meet          : binary_op S 
; prelattice_join_certs   : @sg_CI_certificates S 
; prelattice_meet_certs   : @sg_CI_certificates S 
; prelattice_id_ann_certs : @id_ann_certificates S 
; prelattice_certs        : @lattice_certificates S 
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

Record selective_distributive_prelattice_with_zero {S : Type} := {
  selective_distributive_prelattice_with_zero_eqv          : @eqv S 
; selective_distributive_prelattice_with_zero_join         : binary_op S 
; selective_distributive_prelattice_with_zero_meet         : binary_op S 
; selective_distributive_prelattice_with_zero_join_certs   : @sg_CS_certificates S
; selective_distributive_prelattice_with_zero_meet_certs   : @sg_CS_certificates S 
; selective_distributive_prelattice_with_zero_id_ann_certs : @pid_is_tann_certificates S
; selective_distributive_prelattice_with_zero_certs        : @distributive_lattice_certificates S
; selective_distributive_prelattice_with_zero_ast          : cas_ast
}.

Record selective_distributive_prelattice_with_one {S : Type} := {
  selective_distributive_prelattice_with_one_eqv          : @eqv S 
; selective_distributive_prelattice_with_one_join         : binary_op S 
; selective_distributive_prelattice_with_one_meet         : binary_op S 
; selective_distributive_prelattice_with_one_join_certs   : @sg_CS_certificates S
; selective_distributive_prelattice_with_one_meet_certs   : @sg_CS_certificates S 
; selective_distributive_prelattice_with_one_id_ann_certs : @pann_is_tid_certificates S
; selective_distributive_prelattice_with_one_certs        : @distributive_lattice_certificates S
; selective_distributive_prelattice_with_one_ast          : cas_ast
}.

Record selective_distributive_lattice {S : Type} := {
  selective_distributive_lattice_eqv        : @eqv S 
; selective_distributive_lattice_join       : binary_op S 
; selective_distributive_lattice_meet       : binary_op S 
; selective_distributive_lattice_join_certs : @sg_CS_certificates S 
; selective_distributive_lattice_meet_certs : @sg_CS_certificates S
; selective_distributive_lattice_id_ann_certs : @dually_bounded_certificates S                                                                  
; selective_distributive_lattice_certs      : @distributive_lattice_certificates S
; selective_distributive_lattice_ast        : cas_ast
}.


Record lattice {S : Type} := {
  lattice_eqv          : @eqv S 
; lattice_join         : binary_op S 
; lattice_meet         : binary_op S 
; lattice_join_certs   : @sg_CI_certificates S 
; lattice_meet_certs   : @sg_CI_certificates S
; lattice_id_ann_certs : @dually_bounded_certificates S
; lattice_certs        : @lattice_certificates S
; lattice_ast          : cas_ast
}.


Record distributive_lattice {S : Type} := {
  distributive_lattice_eqv          : @eqv S 
; distributive_lattice_join         : binary_op S 
; distributive_lattice_meet         : binary_op S 
; distributive_lattice_join_certs   : @sg_CI_certificates S 
; distributive_lattice_meet_certs   : @sg_CI_certificates S
; distributive_lattice_id_ann_certs : @dually_bounded_certificates S
; distributive_lattice_certs        : @distributive_lattice_certificates S
; distributive_lattice_ast          : cas_ast
}.
  
End CAS. 







Section Translation. 

Definition P2C_id_ann (S : Type) (r : brel S) (b1 b2 : binary_op S) (P : id_ann_proofs S r b1 b2) : 
              @id_ann_certificates S := 
{|
  id_ann_plus_times_d := p2c_exists_id_ann _ _ b1 b2 (A_id_ann_plus_times_d _ _ _ _ P)
; id_ann_times_plus_d := p2c_exists_id_ann _ _ b2 b1 (A_id_ann_times_plus_d _ _ _ _ P)
|}.

Definition P2C_dually_bounded (S : Type) (r : brel S) (b1 b2 : binary_op S) (R : dually_bounded_proofs S r b1 b2) :
      @dually_bounded_certificates S := 
{|
  bounded_plus_id_is_times_ann := p2c_exists_id_ann_equal _ _ b1 b2 (A_bounded_plus_id_is_times_ann S r b1 b2 R)
; bounded_times_id_is_plus_ann := p2c_exists_id_ann_equal _ _ b2 b1  (A_bounded_times_id_is_plus_ann S r b1 b2 R)
|}.

Definition P2C_pid_is_tann (S : Type) (r : brel S) (b1 b2 : binary_op S) (P : pid_is_tann_proofs S r b1 b2) :
      @pid_is_tann_certificates S := 
{|
  pid_is_tann_plus_times   := p2c_exists_id_ann_equal _ _ b1 b2 (A_pid_is_tann_plus_times S r b1 b2 P)
; pid_is_tann_times_plus_d := p2c_exists_id_ann _ _ b2 b1 (A_pid_is_tann_times_plus_d _ _ _ _ P)
|}.

Definition P2C_pann_is_tid (S : Type) (r : brel S) (b1 b2 : binary_op S) (P : pann_is_tid_proofs S r b1 b2) :
      @pann_is_tid_certificates S := 
{|
  pann_is_tid_plus_times_d   := p2c_exists_id_ann _ _ b1 b2 (A_pann_is_tid_plus_times_d _ _ _ _ P)
; pann_is_tid_times_plus     := p2c_exists_id_ann_equal _ _ b2 b1 (A_pann_is_tid_times_plus S r b1 b2 P)
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


(* for downcasting 

why here? where used? 
*) 

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
; semiring_id_ann_certs := P2C_pid_is_tann S (A_eqv_eq S (A_semiring_eqv S R)) 
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
; selective_semiring_id_ann_certs := P2C_pid_is_tann S (A_eqv_eq S (A_selective_semiring_eqv S R)) 
                                   (A_selective_semiring_plus S R) 
                                   (A_selective_semiring_times S R) 
                                   (A_selective_semiring_id_ann_proofs S R)         
; selective_semiring_certs       := P2C_semiring S (A_eqv_eq S (A_selective_semiring_eqv S R)) 
                                   (A_selective_semiring_plus S R) 
                                   (A_selective_semiring_times S R) 
                                   (A_selective_semiring_proofs S R)
; selective_semiring_ast        := A_selective_semiring_ast S R
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
; lattice_id_ann_certs := P2C_dually_bounded S (A_eqv_eq S (A_lattice_eqv S R)) 
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
; distributive_lattice_id_ann_certs := P2C_dually_bounded S (A_eqv_eq S (A_distributive_lattice_eqv S R)) 
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


Definition A2C_selective_distributive_prelattice_with_zero : ∀ (S : Type), A_selective_distributive_prelattice_with_zero S -> @selective_distributive_prelattice_with_zero S 
:= λ S R,
{|
  selective_distributive_prelattice_with_zero_eqv         := A2C_eqv S (A_selective_distributive_prelattice_with_zero_eqv S R)
; selective_distributive_prelattice_with_zero_join        := A_selective_distributive_prelattice_with_zero_join S R 
; selective_distributive_prelattice_with_zero_meet        := A_selective_distributive_prelattice_with_zero_meet S R 
; selective_distributive_prelattice_with_zero_join_certs  := P2C_sg_CS S (A_eqv_eq S (A_selective_distributive_prelattice_with_zero_eqv S R)) 
                                (A_selective_distributive_prelattice_with_zero_join S R) 
                                (A_selective_distributive_prelattice_with_zero_join_proofs S R)
; selective_distributive_prelattice_with_zero_meet_certs := P2C_sg_CS S (A_eqv_eq S (A_selective_distributive_prelattice_with_zero_eqv S R)) 
                                (A_selective_distributive_prelattice_with_zero_meet S R) 
                                (A_selective_distributive_prelattice_with_zero_meet_proofs S R)
; selective_distributive_prelattice_with_zero_id_ann_certs := P2C_pid_is_tann S (A_eqv_eq S (A_selective_distributive_prelattice_with_zero_eqv S R)) 
                                   (A_selective_distributive_prelattice_with_zero_join S R) 
                                   (A_selective_distributive_prelattice_with_zero_meet S R) 
                                   (A_selective_distributive_prelattice_with_zero_id_ann_proofs S R)         

; selective_distributive_prelattice_with_zero_certs       := P2C_distributive_lattice S 
                                        (A_eqv_eq S (A_selective_distributive_prelattice_with_zero_eqv S R)) 
                                        (A_selective_distributive_prelattice_with_zero_join S R)
                                        (A_selective_distributive_prelattice_with_zero_meet S R)                   
                                        (A_selective_distributive_prelattice_with_zero_proofs S R)
; selective_distributive_prelattice_with_zero_ast        := A_selective_distributive_prelattice_with_zero_ast S R
|}.


Definition A2C_selective_distributive_prelattice_with_one : ∀ (S : Type), A_selective_distributive_prelattice_with_one S -> @selective_distributive_prelattice_with_one S 
:= λ S R,
{|
  selective_distributive_prelattice_with_one_eqv         := A2C_eqv S (A_selective_distributive_prelattice_with_one_eqv S R)
; selective_distributive_prelattice_with_one_join        := A_selective_distributive_prelattice_with_one_join S R 
; selective_distributive_prelattice_with_one_meet        := A_selective_distributive_prelattice_with_one_meet S R 
; selective_distributive_prelattice_with_one_join_certs  := P2C_sg_CS S (A_eqv_eq S (A_selective_distributive_prelattice_with_one_eqv S R)) 
                                (A_selective_distributive_prelattice_with_one_join S R) 
                                (A_selective_distributive_prelattice_with_one_join_proofs S R)
; selective_distributive_prelattice_with_one_meet_certs := P2C_sg_CS S (A_eqv_eq S (A_selective_distributive_prelattice_with_one_eqv S R)) 
                                (A_selective_distributive_prelattice_with_one_meet S R) 
                                (A_selective_distributive_prelattice_with_one_meet_proofs S R)
; selective_distributive_prelattice_with_one_id_ann_certs := P2C_pann_is_tid S (A_eqv_eq S (A_selective_distributive_prelattice_with_one_eqv S R)) 
                                   (A_selective_distributive_prelattice_with_one_join S R) 
                                   (A_selective_distributive_prelattice_with_one_meet S R) 
                                   (A_selective_distributive_prelattice_with_one_id_ann_proofs S R)         

; selective_distributive_prelattice_with_one_certs       := P2C_distributive_lattice S 
                                        (A_eqv_eq S (A_selective_distributive_prelattice_with_one_eqv S R)) 
                                        (A_selective_distributive_prelattice_with_one_join S R)
                                        (A_selective_distributive_prelattice_with_one_meet S R)                   
                                        (A_selective_distributive_prelattice_with_one_proofs S R)
; selective_distributive_prelattice_with_one_ast        := A_selective_distributive_prelattice_with_one_ast S R
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
; selective_distributive_lattice_id_ann_certs := P2C_dually_bounded S (A_eqv_eq S (A_selective_distributive_lattice_eqv S R)) 
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



Definition P2C_dioid (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) (P : dioid_proofs S eq plus times) := 
{|
  dioid_left_distributive      := @Assert_Left_Distributive S
; dioid_right_distributive     := @Assert_Right_Distributive S
; dioid_left_left_absorptive   := @Assert_Left_Left_Absorptive S
; dioid_left_right_absorptive  := @Assert_Left_Right_Absorptive S
|}.



Definition A2C_pre_dioid (S : Type) (P : A_pre_dioid S) := 
{|
  pre_dioid_eqv           := A2C_eqv S (A_pre_dioid_eqv S P)
; pre_dioid_plus          := A_pre_dioid_plus S P 
; pre_dioid_times         := A_pre_dioid_times S P 
; pre_dioid_plus_certs   := P2C_sg_CI S _ _ (A_pre_dioid_plus_proofs S P)
; pre_dioid_times_certs  := P2C_msg S _ _  (A_pre_dioid_times_proofs S P) 
; pre_dioid_id_ann_certs := P2C_id_ann S _ _ _ (A_pre_dioid_id_ann_proofs S P) 
; pre_dioid_certs        := P2C_dioid S _ _ _ (A_pre_dioid_proofs S P) 
; pre_dioid_ast           := A_pre_dioid_ast S P
|}.



Definition A2C_pre_dioid_with_one (S : Type) (P : A_pre_dioid_with_one S) := 
{|
  pre_dioid_with_one_eqv           := A2C_eqv S (A_pre_dioid_with_one_eqv S P)
; pre_dioid_with_one_plus          := A_pre_dioid_with_one_plus S P 
; pre_dioid_with_one_times         := A_pre_dioid_with_one_times S P 
; pre_dioid_with_one_plus_certs   := P2C_sg_CI S _ _ (A_pre_dioid_with_one_plus_proofs S P)
; pre_dioid_with_one_times_certs  := P2C_msg S _ _  (A_pre_dioid_with_one_times_proofs S P) 
; pre_dioid_with_one_id_ann_certs := P2C_pann_is_tid S _ _ _ (A_pre_dioid_with_one_id_ann_proofs S P) 
; pre_dioid_with_one_certs        := P2C_dioid S _ _ _ (A_pre_dioid_with_one_proofs S P) 
; pre_dioid_with_one_ast           := A_pre_dioid_with_one_ast S P
|}.


Definition A2C_pre_dioid_with_zero (S : Type) (P : A_pre_dioid_with_zero S) := 
{|
  pre_dioid_with_zero_eqv           := A2C_eqv S (A_pre_dioid_with_zero_eqv S P)
; pre_dioid_with_zero_plus          := A_pre_dioid_with_zero_plus S P 
; pre_dioid_with_zero_times         := A_pre_dioid_with_zero_times S P 
; pre_dioid_with_zero_plus_certs   := P2C_sg_CI S _ _ (A_pre_dioid_with_zero_plus_proofs S P)
; pre_dioid_with_zero_times_certs  := P2C_msg S _ _  (A_pre_dioid_with_zero_times_proofs S P) 
; pre_dioid_with_zero_id_ann_certs := P2C_pid_is_tann S _ _ _ (A_pre_dioid_with_zero_id_ann_proofs S P) 
; pre_dioid_with_zero_certs        := P2C_dioid S _ _ _ (A_pre_dioid_with_zero_proofs S P) 
; pre_dioid_with_zero_ast           := A_pre_dioid_with_zero_ast S P
|}.



Definition A2C_dioid (S : Type) (P : A_dioid S) := 
{|
  dioid_eqv           := A2C_eqv S (A_dioid_eqv S P)
; dioid_plus          := A_dioid_plus S P 
; dioid_times         := A_dioid_times S P 
; dioid_plus_certs   := P2C_sg_CI S _ _ (A_dioid_plus_proofs S P)
; dioid_times_certs  := P2C_msg S _ _  (A_dioid_times_proofs S P) 
; dioid_id_ann_certs := P2C_dually_bounded S _ _ _ (A_dioid_id_ann_proofs S P) 
; dioid_certs        := P2C_dioid S _ _ _ (A_dioid_proofs S P) 
; dioid_ast           := A_dioid_ast S P
|}.


Definition A2C_selective_pre_dioid (S : Type) (P : A_selective_pre_dioid S) :=
{|  
  selective_pre_dioid_eqv           := A2C_eqv S (A_selective_pre_dioid_eqv S P)
; selective_pre_dioid_plus          := A_selective_pre_dioid_plus S P 
; selective_pre_dioid_times         := A_selective_pre_dioid_times S P  
; selective_pre_dioid_plus_certs    := P2C_sg_CS S _ _ (A_selective_pre_dioid_plus_proofs S P)
; selective_pre_dioid_times_certs   := P2C_msg S _ _  (A_selective_pre_dioid_times_proofs S P) 
; selective_pre_dioid_id_ann_certs  := P2C_id_ann S _ _ _ (A_selective_pre_dioid_id_ann_proofs S P) 
; selective_pre_dioid_certs         := P2C_dioid S _ _ _ (A_selective_pre_dioid_proofs S P) 
; selective_pre_dioid_ast           := A_selective_pre_dioid_ast S P
|}.

Definition A2C_selective_pre_dioid_with_one (S : Type) (P : A_selective_pre_dioid_with_one S) :=
{|  
  selective_pre_dioid_with_one_eqv           := A2C_eqv S (A_selective_pre_dioid_with_one_eqv S P)
; selective_pre_dioid_with_one_plus          := A_selective_pre_dioid_with_one_plus S P 
; selective_pre_dioid_with_one_times         := A_selective_pre_dioid_with_one_times S P 
; selective_pre_dioid_with_one_plus_certs    := P2C_sg_CS S _ _ (A_selective_pre_dioid_with_one_plus_proofs S P)
; selective_pre_dioid_with_one_times_certs   := P2C_msg S _ _  (A_selective_pre_dioid_with_one_times_proofs S P) 
; selective_pre_dioid_with_one_id_ann_certs  := P2C_pann_is_tid S _ _ _ (A_selective_pre_dioid_with_one_id_ann_proofs S P) 
; selective_pre_dioid_with_one_certs         := P2C_dioid S _ _ _ (A_selective_pre_dioid_with_one_proofs S P) 
; selective_pre_dioid_with_one_ast           := A_selective_pre_dioid_with_one_ast S P
|}.

Definition A2C_selective_pre_dioid_with_zero (S : Type) (P : A_selective_pre_dioid_with_zero S) := 
{|
  selective_pre_dioid_with_zero_eqv           := A2C_eqv S (A_selective_pre_dioid_with_zero_eqv S P) 
; selective_pre_dioid_with_zero_plus          := A_selective_pre_dioid_with_zero_plus S P  
; selective_pre_dioid_with_zero_times         := A_selective_pre_dioid_with_zero_times S P  
; selective_pre_dioid_with_zero_plus_certs    := P2C_sg_CS S _ _ (A_selective_pre_dioid_with_zero_plus_proofs S P) 
; selective_pre_dioid_with_zero_times_certs   := P2C_msg S _ _  (A_selective_pre_dioid_with_zero_times_proofs S P)  
; selective_pre_dioid_with_zero_id_ann_certs  := P2C_pid_is_tann S _ _ _ (A_selective_pre_dioid_with_zero_id_ann_proofs S P) 
; selective_pre_dioid_with_zero_certs         := P2C_dioid S _ _ _ (A_selective_pre_dioid_with_zero_proofs S P)  
; selective_pre_dioid_with_zero_ast           := A_selective_pre_dioid_with_zero_ast S P 
|}.


Definition A2C_selective_dioid (S : Type) (P : A_selective_dioid S) := 
{|
  selective_dioid_eqv           := A2C_eqv S (A_selective_dioid_eqv S P)
; selective_dioid_plus          := A_selective_dioid_plus S P 
; selective_dioid_times         := A_selective_dioid_times S P 
; selective_dioid_plus_certs   := P2C_sg_CS S _ _ (A_selective_dioid_plus_proofs S P)
; selective_dioid_times_certs  := P2C_msg S _ _  (A_selective_dioid_times_proofs S P) 
; selective_dioid_id_ann_certs := P2C_dually_bounded S _ _ _ (A_selective_dioid_id_ann_proofs S P) 
; selective_dioid_certs        := P2C_dioid S _ _ _ (A_selective_dioid_proofs S P) 
; selective_dioid_ast           := A_selective_dioid_ast S P
|}.



Definition A2C_selective_cancellative_pre_dioid (S : Type) (P : A_selective_cancellative_pre_dioid S) :=
{|  
  selective_cancellative_pre_dioid_eqv           := A2C_eqv S (A_selective_cancellative_pre_dioid_eqv S P)
; selective_cancellative_pre_dioid_plus          := A_selective_cancellative_pre_dioid_plus S P 
; selective_cancellative_pre_dioid_times         := A_selective_cancellative_pre_dioid_times S P  
; selective_cancellative_pre_dioid_plus_certs    := P2C_sg_CS S _ _ (A_selective_cancellative_pre_dioid_plus_proofs S P)
; selective_cancellative_pre_dioid_times_certs   := P2C_sg_CK S _ _  (A_selective_cancellative_pre_dioid_times_proofs S P) 
; selective_cancellative_pre_dioid_id_ann_certs  := P2C_id_ann S _ _ _ (A_selective_cancellative_pre_dioid_id_ann_proofs S P) 
; selective_cancellative_pre_dioid_certs         := P2C_dioid S _ _ _ (A_selective_cancellative_pre_dioid_proofs S P) 
; selective_cancellative_pre_dioid_ast           := A_selective_cancellative_pre_dioid_ast S P
|}.

Definition A2C_selective_cancellative_pre_dioid_with_one (S : Type) (P : A_selective_cancellative_pre_dioid_with_one S) :=
{|  
  selective_cancellative_pre_dioid_with_one_eqv           := A2C_eqv S (A_selective_cancellative_pre_dioid_with_one_eqv S P)
; selective_cancellative_pre_dioid_with_one_plus          := A_selective_cancellative_pre_dioid_with_one_plus S P 
; selective_cancellative_pre_dioid_with_one_times         := A_selective_cancellative_pre_dioid_with_one_times S P 
; selective_cancellative_pre_dioid_with_one_plus_certs    := P2C_sg_CS S _ _ (A_selective_cancellative_pre_dioid_with_one_plus_proofs S P)
; selective_cancellative_pre_dioid_with_one_times_certs   := P2C_sg_CK S _ _  (A_selective_cancellative_pre_dioid_with_one_times_proofs S P) 
; selective_cancellative_pre_dioid_with_one_id_ann_certs  := P2C_pann_is_tid S _ _ _ (A_selective_cancellative_pre_dioid_with_one_id_ann_proofs S P) 
; selective_cancellative_pre_dioid_with_one_certs         := P2C_dioid S _ _ _ (A_selective_cancellative_pre_dioid_with_one_proofs S P) 
; selective_cancellative_pre_dioid_with_one_ast           := A_selective_cancellative_pre_dioid_with_one_ast S P
|}.

Definition A2C_selective_cancellative_pre_dioid_with_zero (S : Type) (P : A_selective_cancellative_pre_dioid_with_zero S) := 
{|
  selective_cancellative_pre_dioid_with_zero_eqv           := A2C_eqv S (A_selective_cancellative_pre_dioid_with_zero_eqv S P) 
; selective_cancellative_pre_dioid_with_zero_plus          := A_selective_cancellative_pre_dioid_with_zero_plus S P  
; selective_cancellative_pre_dioid_with_zero_times         := A_selective_cancellative_pre_dioid_with_zero_times S P  
; selective_cancellative_pre_dioid_with_zero_plus_certs    := P2C_sg_CS S _ _ (A_selective_cancellative_pre_dioid_with_zero_plus_proofs S P) 
; selective_cancellative_pre_dioid_with_zero_times_certs   := P2C_sg_CK S _ _  (A_selective_cancellative_pre_dioid_with_zero_times_proofs S P)  
; selective_cancellative_pre_dioid_with_zero_id_ann_certs  := P2C_pid_is_tann S _ _ _ (A_selective_cancellative_pre_dioid_with_zero_id_ann_proofs S P) 
; selective_cancellative_pre_dioid_with_zero_certs         := P2C_dioid S _ _ _ (A_selective_cancellative_pre_dioid_with_zero_proofs S P)  
; selective_cancellative_pre_dioid_with_zero_ast           := A_selective_cancellative_pre_dioid_with_zero_ast S P 
|}.


Definition A2C_selective_cancellative_dioid (S : Type) (P : A_selective_cancellative_dioid S) := 
{|
  selective_cancellative_dioid_eqv           := A2C_eqv S (A_selective_cancellative_dioid_eqv S P)
; selective_cancellative_dioid_plus          := A_selective_cancellative_dioid_plus S P 
; selective_cancellative_dioid_times         := A_selective_cancellative_dioid_times S P 
; selective_cancellative_dioid_plus_certs   := P2C_sg_CS S _ _ (A_selective_cancellative_dioid_plus_proofs S P)
; selective_cancellative_dioid_times_certs  := P2C_sg_CK S _ _  (A_selective_cancellative_dioid_times_proofs S P) 
; selective_cancellative_dioid_id_ann_certs := P2C_dually_bounded S _ _ _ (A_selective_cancellative_dioid_id_ann_proofs S P) 
; selective_cancellative_dioid_certs        := P2C_dioid S _ _ _ (A_selective_cancellative_dioid_proofs S P) 
; selective_cancellative_dioid_ast           := A_selective_cancellative_dioid_ast S P
|}.

End Translation. 



Section MCAS.

Inductive bs_mcas {S : Type} :=
| BS_Error : string               -> @bs_mcas S
| BS_bs : @bs S                   -> @bs_mcas S
| BS_bs_CI : @bs_CI S              -> @bs_mcas S                                   
| BS_bs_CS : @bs_CS S              -> @bs_mcas S                                     
| BS_presemiring  : @presemiring S -> @bs_mcas S
| BS_semiring  : @semiring S       -> @bs_mcas S
| BS_pre_dioid  : @pre_dioid S     -> @bs_mcas S
| BS_pre_dioid_with_one  : @pre_dioid_with_one S -> @bs_mcas S
| BS_pre_dioid_with_zero  : @pre_dioid_with_zero S -> @bs_mcas S
| BS_dioid  : @dioid S              -> @bs_mcas S
| BS_prelattice  : @prelattice S -> @bs_mcas S
| BS_distributive_prelattice  : @distributive_prelattice S -> @bs_mcas S
| BS_lattice  : @lattice S          -> @bs_mcas S
| BS_distributive_lattice  : @distributive_lattice S -> @bs_mcas S
| BS_selective_presemiring  : @selective_presemiring S -> @bs_mcas S
| BS_selective_semiring  : @selective_semiring S -> @bs_mcas S
| BS_selective_pre_dioid  : @selective_pre_dioid S -> @bs_mcas S
| BS_selective_pre_dioid_with_zero  : @selective_pre_dioid_with_zero S -> @bs_mcas S
| BS_selective_pre_dioid_with_one  : @selective_pre_dioid_with_one S -> @bs_mcas S
| BS_selective_dioid  : @selective_dioid S -> @bs_mcas S                                                                                          
| BS_selective_cancellative_pre_dioid  : @selective_cancellative_pre_dioid S -> @bs_mcas S
| BS_selective_cancellative_pre_dioid_with_zero  : @selective_cancellative_pre_dioid_with_zero S -> @bs_mcas S
| BS_selective_cancellative_pre_dioid_with_one  : @selective_cancellative_pre_dioid_with_one S -> @bs_mcas S
| BS_selective_cancellative_dioid  : @selective_cancellative_dioid S -> @bs_mcas S
| BS_selective_distributive_prelattice  : @selective_distributive_prelattice S -> @bs_mcas S
| BS_selective_distributive_prelattice_with_zero  : @selective_distributive_prelattice_with_zero S -> @bs_mcas S    
| BS_selective_distributive_prelattice_with_one  : @selective_distributive_prelattice_with_one S -> @bs_mcas S
| BS_selective_distributive_lattice  : @selective_distributive_lattice S -> @bs_mcas S
. 

Definition bs_classify {S : Type} (A : @bs S) : @bs_mcas S :=
let ast     := bs_ast A in
let eqv     := bs_eqv A in
let plus    := bs_plus A in      
let plusP   := bs_plus_certs A in
let sel_d   := asg_selective_d plusP in
let idem_d  := asg_idempotent_d plusP in   
let id_annP := bs_id_ann_certs A in
let pid_id_tann_d := id_ann_plus_times_d id_annP in
let tid_id_pann_d := id_ann_times_plus_d id_annP in
let times   := bs_times A in
let timesP  := bs_times_certs A in
let comm_d  := msg_commutative_d timesP in
let left_can_d := msg_left_cancel_d timesP in
let right_can_d := msg_right_cancel_d timesP in
let P       := bs_certs A in
let LD_d := bs_left_distributive_d P in 
let RD_d := bs_right_distributive_d P in 
let LLA_d := bs_left_left_absorptive_d P in 
let LRA_d := bs_left_right_absorptive_d P in
match sel_d with
| Certify_Selective  =>
  (************* Selective *****************)
  let sg_cs_p := {|
                      sg_CS_associative   := Assert_Associative 
                    ; sg_CS_congruence    := Assert_Bop_Congruence 
                    ; sg_CS_commutative   := Assert_Commutative 
                    ; sg_CS_selective     := Assert_Selective 
                  |} in
  let bs_cs := {|
                    bs_CS_eqv          := eqv 
                  ; bs_CS_plus         := plus
                  ; bs_CS_times        := times 
                  ; bs_CS_plus_certs   := sg_cs_p 
                  ; bs_CS_times_certs  := timesP 
                  ; bs_CS_id_ann_certs := id_annP 
                  ; bs_CS_certs        := P 
                  ; bs_CS_ast          := ast 
                  |} in 
  match LD_d with
  | Certify_Left_Distributive  =>
    match RD_d with
    | Certify_Right_Distributive  =>
      match LLA_d, LRA_d with
      | Certify_Left_Left_Absorptive,   Certify_Left_Right_Absorptive =>
        let doid_p :=
            {|
                dioid_left_distributive     := Assert_Left_Distributive
              ; dioid_right_distributive    := Assert_Right_Distributive
              ; dioid_left_left_absorptive  := Assert_Left_Left_Absorptive
              ; dioid_left_right_absorptive := Assert_Left_Right_Absorptive
              |} in
        match pid_id_tann_d, tid_id_pann_d with
        | Id_Ann_Cert_Equal plus_id_is_times_ann, Id_Ann_Cert_Equal times_id_is_plus_ann =>
             BS_selective_dioid 
               {|
                   selective_dioid_eqv := eqv 
                 ; selective_dioid_plus := plus
                 ; selective_dioid_times := times 
                 ; selective_dioid_plus_certs := sg_cs_p 
                 ; selective_dioid_times_certs := timesP  
                 ; selective_dioid_id_ann_certs :=
                     {|
                         bounded_plus_id_is_times_ann := Assert_Exists_Id_Ann_Equal plus_id_is_times_ann
                       ; bounded_times_id_is_plus_ann := Assert_Exists_Id_Ann_Equal times_id_is_plus_ann                      
                     |} 
                 ; selective_dioid_certs := doid_p 
                 ; selective_dioid_ast := ast 
               |} 
        | _ , Id_Ann_Cert_Equal times_id_is_plus_ann =>
              BS_selective_pre_dioid_with_one 
                {|
                   selective_pre_dioid_with_one_eqv := eqv 
                 ; selective_pre_dioid_with_one_plus := plus
                 ; selective_pre_dioid_with_one_times := times 
                 ; selective_pre_dioid_with_one_plus_certs := sg_cs_p 
                 ; selective_pre_dioid_with_one_times_certs := timesP  
                 ; selective_pre_dioid_with_one_id_ann_certs :=
                     {|
                         pann_is_tid_plus_times_d  := pid_id_tann_d
                       ; pann_is_tid_times_plus  := Assert_Exists_Id_Ann_Equal times_id_is_plus_ann  
                     |} 
                 ; selective_pre_dioid_with_one_certs := doid_p 
                 ; selective_pre_dioid_with_one_ast := ast 
                |} 
        | Id_Ann_Cert_Equal plus_id_is_times_ann, _ =>
             BS_selective_pre_dioid_with_zero
                {|
                   selective_pre_dioid_with_zero_eqv := eqv 
                 ; selective_pre_dioid_with_zero_plus := plus
                 ; selective_pre_dioid_with_zero_times := times 
                 ; selective_pre_dioid_with_zero_plus_certs := sg_cs_p 
                 ; selective_pre_dioid_with_zero_times_certs := timesP  
                 ; selective_pre_dioid_with_zero_id_ann_certs :=
                     {|
                         pid_is_tann_plus_times   := Assert_Exists_Id_Ann_Equal plus_id_is_times_ann
                       ; pid_is_tann_times_plus_d := tid_id_pann_d                     
                     |} 
                 ; selective_pre_dioid_with_zero_certs := doid_p 
                 ; selective_pre_dioid_with_zero_ast := ast 
                |} 
        | _, _ => BS_selective_pre_dioid 
               {|
                   selective_pre_dioid_eqv := eqv 
                 ; selective_pre_dioid_plus := plus
                 ; selective_pre_dioid_times := times 
                 ; selective_pre_dioid_plus_certs := sg_cs_p 
                 ; selective_pre_dioid_times_certs := timesP  
                 ; selective_pre_dioid_id_ann_certs := id_annP
                 ; selective_pre_dioid_certs := doid_p 
                 ; selective_pre_dioid_ast := ast 
               |} 
        end
      | _, _ => BS_bs_CS bs_cs  (* selective semiring? *) 
      end 
    | _ => BS_bs_CS bs_cs (* not RD *) 
    end 
  | _ => BS_bs_CS bs_cs (* not LD *) 
  end 
| Certify_Not_Selective nsel =>
  match idem_d with
  | Certify_Idempotent =>
    (************* Idempotent, Not Selective *****************)
    let sg_ci_p := {|
                     sg_CI_associative    := Assert_Associative
                    ; sg_CI_congruence    := Assert_Bop_Congruence 
                    ; sg_CI_commutative   := Assert_Commutative 
                    ; sg_CI_idempotent    := Assert_Idempotent 
                    ; sg_CI_not_selective := Assert_Not_Selective nsel 
                  |} in
    let bs_ci := {|
                    bs_CI_eqv           := eqv 
                  ; bs_CI_plus          := plus
                  ; bs_CI_times         := times 
                  ; bs_CI_plus_certs   := sg_ci_p 
                  ; bs_CI_times_certs  := timesP 
                  ; bs_CI_id_ann_certs := id_annP 
                  ; bs_CI_certs        := P 
                  ; bs_CI_ast           := ast 
                  |} in 
    match LD_d with
    | Certify_Left_Distributive  =>
      match RD_d with
      | Certify_Right_Distributive  =>
        match LLA_d with
        | Certify_Left_Left_Absorptive =>  
          match LRA_d with
          | Certify_Left_Right_Absorptive =>
            let doid_p := {|
                            dioid_left_distributive      := Assert_Left_Distributive
                           ; dioid_right_distributive    := Assert_Right_Distributive
                           ; dioid_left_left_absorptive  := Assert_Left_Left_Absorptive
                           ; dioid_left_right_absorptive := Assert_Left_Right_Absorptive
                |} in
            match pid_id_tann_d, tid_id_pann_d with
            | Id_Ann_Cert_Equal plus_id_is_times_ann, Id_Ann_Cert_Equal times_id_is_plus_ann =>
              BS_dioid   {|
                             dioid_eqv := eqv 
                           ; dioid_plus := plus
                           ; dioid_times := times 
                           ; dioid_plus_certs := sg_ci_p 
                           ; dioid_times_certs := timesP  
                           ; dioid_id_ann_certs :=
                               {|
                                   bounded_plus_id_is_times_ann := Assert_Exists_Id_Ann_Equal plus_id_is_times_ann
                                 ; bounded_times_id_is_plus_ann := Assert_Exists_Id_Ann_Equal times_id_is_plus_ann                      
                               |} 
                           ; dioid_certs := doid_p 
                           ; dioid_ast := ast 
                           |} 
            | _ , Id_Ann_Cert_Equal times_id_is_plus_ann =>
              BS_pre_dioid_with_one  {|
                                        pre_dioid_with_one_eqv := eqv 
                                        ; pre_dioid_with_one_plus := plus
                                        ; pre_dioid_with_one_times := times 
                                        ; pre_dioid_with_one_plus_certs := sg_ci_p 
                                        ; pre_dioid_with_one_times_certs := timesP  
                                        ; pre_dioid_with_one_id_ann_certs :=
                                            {|
                                                pann_is_tid_plus_times_d  := pid_id_tann_d
                                              ; pann_is_tid_times_plus := Assert_Exists_Id_Ann_Equal times_id_is_plus_ann                                             
                                            |} 
                                        ; pre_dioid_with_one_certs := doid_p 
                                        ; pre_dioid_with_one_ast := ast 
                           |} 
            | Id_Ann_Cert_Equal plus_id_is_times_ann, _ =>
              BS_pre_dioid_with_zero  {|
                                         pre_dioid_with_zero_eqv := eqv 
                                         ; pre_dioid_with_zero_plus := plus
                                         ; pre_dioid_with_zero_times := times 
                                         ; pre_dioid_with_zero_plus_certs := sg_ci_p 
                                         ; pre_dioid_with_zero_times_certs := timesP  
                                         ; pre_dioid_with_zero_id_ann_certs :=
                                             {|
                                               pid_is_tann_plus_times   := Assert_Exists_Id_Ann_Equal plus_id_is_times_ann
                                              ; pid_is_tann_times_plus_d := tid_id_pann_d                     
                                             |} 
                                         ; pre_dioid_with_zero_certs := doid_p 
                                         ; pre_dioid_with_zero_ast := ast 
                           |} 
            | _, _ => BS_pre_dioid  {|
                                       pre_dioid_eqv := eqv 
                                       ; pre_dioid_plus := plus
                                       ; pre_dioid_times := times 
                                       ; pre_dioid_plus_certs := sg_ci_p 
                                       ; pre_dioid_times_certs := timesP  
                                       ; pre_dioid_id_ann_certs := id_annP
                                       ; pre_dioid_certs := doid_p 
                                       ; pre_dioid_ast := ast                                        
                                       |} 
            end
          |  _ => BS_bs_CI bs_ci (* not LRA *) 
          end 
        | _  => BS_bs_CI bs_ci (* not LLA *) 
        end 
      | _      => BS_bs_CI bs_ci
      end 
    |      _ => BS_bs_CI bs_ci 
    end 
  | Certify_Not_Idempotent nidem =>
  (************* Not Idempotent *****************)         
    match LD_d with
    | Certify_Left_Distributive =>
      match RD_d with
      | Certify_Right_Distributive => BS_bs A (* No, check for semiring *) 
      | _      => BS_bs A 
      end 
    |      _ => BS_bs A 
    end 
  end 
end.


End MCAS.   
