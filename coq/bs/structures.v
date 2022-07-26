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
; A_bs_plus_proofs   : sg_proofs S (A_eqv_eq S A_bs_eqv) A_bs_plus    (* sg_C_proofs *)
; A_bs_times_proofs  : sg_proofs S (A_eqv_eq S A_bs_eqv) A_bs_times   
; A_bs_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_bs_eqv) A_bs_plus A_bs_times                                 
; A_bs_proofs        : bs_proofs S (A_eqv_eq S A_bs_eqv) A_bs_plus A_bs_times
; A_bs_ast           : cas_bs_ast
}.


Record A_bs_CS (S : Type) := {
  A_bs_CS_eqv           : A_eqv S 
; A_bs_CS_plus          : binary_op S 
; A_bs_CS_times         : binary_op S 
; A_bs_CS_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus
; A_bs_CS_times_proofs  : sg_proofs S    (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_times
; A_bs_CS_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus A_bs_CS_times
; A_bs_CS_proofs        : bs_proofs S (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus A_bs_CS_times
; A_bs_CS_ast           : cas_bs_ast
}.

Record A_bs_CI (S : Type) := {
  A_bs_CI_eqv           : A_eqv S 
; A_bs_CI_plus          : binary_op S 
; A_bs_CI_times         : binary_op S 
; A_bs_CI_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_plus
; A_bs_CI_times_proofs  : sg_proofs S    (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_times
; A_bs_CI_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_plus A_bs_CI_times
; A_bs_CI_proofs        : bs_proofs S (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_plus A_bs_CI_times
; A_bs_CI_ast           : cas_bs_ast
}.

Record A_presemiring (S : Type) := {
  A_presemiring_eqv           : A_eqv S 
; A_presemiring_plus          : binary_op S 
; A_presemiring_times         : binary_op S 
; A_presemiring_plus_proofs   : sg_C_proofs S (A_eqv_eq S A_presemiring_eqv) A_presemiring_plus
; A_presemiring_times_proofs  : sg_proofs S   (A_eqv_eq S A_presemiring_eqv) A_presemiring_times
; A_presemiring_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_presemiring_eqv) A_presemiring_plus A_presemiring_times
; A_presemiring_proofs        : semiring_proofs S (A_eqv_eq S A_presemiring_eqv) A_presemiring_plus A_presemiring_times
; A_presemiring_ast           : cas_bs_ast
}.
Record A_semiring (S : Type) := {
  A_semiring_eqv           : A_eqv S 
; A_semiring_plus          : binary_op S 
; A_semiring_times         : binary_op S 
; A_semiring_plus_proofs   : sg_C_proofs S (A_eqv_eq S A_semiring_eqv) A_semiring_plus
; A_semiring_times_proofs  : sg_proofs S   (A_eqv_eq S A_semiring_eqv) A_semiring_times
; A_semiring_id_ann_proofs : pid_is_tann_proofs S (A_eqv_eq S A_semiring_eqv) A_semiring_plus A_semiring_times
; A_semiring_proofs        : semiring_proofs S (A_eqv_eq S A_semiring_eqv) A_semiring_plus A_semiring_times
; A_semiring_ast           : cas_bs_ast
}.


Record A_pre_dioid (S : Type) := {
  A_pre_dioid_eqv           : A_eqv S 
; A_pre_dioid_plus          : binary_op S 
; A_pre_dioid_times         : binary_op S 
; A_pre_dioid_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_pre_dioid_eqv) A_pre_dioid_plus
; A_pre_dioid_times_proofs  : sg_proofs S   (A_eqv_eq S A_pre_dioid_eqv) A_pre_dioid_times
; A_pre_dioid_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_pre_dioid_eqv) A_pre_dioid_plus A_pre_dioid_times
; A_pre_dioid_proofs        : dioid_proofs S (A_eqv_eq S A_pre_dioid_eqv) A_pre_dioid_plus A_pre_dioid_times
; A_pre_dioid_ast           : cas_bs_ast
}.


Record A_pre_dioid_with_one (S : Type) := {
  A_pre_dioid_with_one_eqv           : A_eqv S 
; A_pre_dioid_with_one_plus          : binary_op S 
; A_pre_dioid_with_one_times         : binary_op S 
; A_pre_dioid_with_one_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_pre_dioid_with_one_eqv) A_pre_dioid_with_one_plus
; A_pre_dioid_with_one_times_proofs  : sg_proofs S   (A_eqv_eq S A_pre_dioid_with_one_eqv) A_pre_dioid_with_one_times
; A_pre_dioid_with_one_id_ann_proofs : pann_is_tid_proofs S (A_eqv_eq S A_pre_dioid_with_one_eqv) A_pre_dioid_with_one_plus A_pre_dioid_with_one_times
; A_pre_dioid_with_one_proofs        : dioid_proofs S (A_eqv_eq S A_pre_dioid_with_one_eqv) A_pre_dioid_with_one_plus A_pre_dioid_with_one_times
; A_pre_dioid_with_one_ast           : cas_bs_ast
}.



Record A_pre_dioid_with_zero (S : Type) := {
  A_pre_dioid_with_zero_eqv           : A_eqv S 
; A_pre_dioid_with_zero_plus          : binary_op S 
; A_pre_dioid_with_zero_times         : binary_op S 
; A_pre_dioid_with_zero_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_pre_dioid_with_zero_eqv) A_pre_dioid_with_zero_plus
; A_pre_dioid_with_zero_times_proofs  : sg_proofs S   (A_eqv_eq S A_pre_dioid_with_zero_eqv) A_pre_dioid_with_zero_times
; A_pre_dioid_with_zero_id_ann_proofs : pid_is_tann_proofs S (A_eqv_eq S A_pre_dioid_with_zero_eqv) A_pre_dioid_with_zero_plus A_pre_dioid_with_zero_times
; A_pre_dioid_with_zero_proofs        : dioid_proofs S (A_eqv_eq S A_pre_dioid_with_zero_eqv) A_pre_dioid_with_zero_plus A_pre_dioid_with_zero_times
; A_pre_dioid_with_zero_ast           : cas_bs_ast
}.


Record A_dioid (S : Type) := {
  A_dioid_eqv           : A_eqv S 
; A_dioid_plus          : binary_op S 
; A_dioid_times         : binary_op S 
; A_dioid_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus
; A_dioid_times_proofs  : sg_proofs S   (A_eqv_eq S A_dioid_eqv) A_dioid_times
; A_dioid_id_ann_proofs : dually_bounded_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus A_dioid_times
; A_dioid_proofs        : dioid_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus A_dioid_times
; A_dioid_ast           : cas_bs_ast
}.


Record A_prelattice (S : Type) := {
  A_prelattice_eqv           : A_eqv S 
; A_prelattice_join          : binary_op S 
; A_prelattice_meet          : binary_op S 
; A_prelattice_join_proofs   : sg_CI_proofs S (A_eqv_eq S A_prelattice_eqv) A_prelattice_join
; A_prelattice_meet_proofs   : sg_CI_proofs S (A_eqv_eq S A_prelattice_eqv) A_prelattice_meet
; A_prelattice_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_prelattice_eqv) A_prelattice_join A_prelattice_meet      
; A_prelattice_proofs        : lattice_proofs S (A_eqv_eq S A_prelattice_eqv) A_prelattice_join A_prelattice_meet
; A_prelattice_ast           : cas_bs_ast
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
; A_distributive_prelattice_ast         : cas_bs_ast
}.


Record A_lattice (S : Type) := {
  A_lattice_eqv           : A_eqv S 
; A_lattice_join          : binary_op S 
; A_lattice_meet          : binary_op S 
; A_lattice_join_proofs   : sg_CI_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_join
; A_lattice_meet_proofs   : sg_CI_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_meet
; A_lattice_id_ann_proofs : dually_bounded_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_join A_lattice_meet      
; A_lattice_proofs        : lattice_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_join A_lattice_meet
; A_lattice_ast           : cas_bs_ast
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
; A_distributive_lattice_ast         : cas_bs_ast
}.

Record A_selective_presemiring (S : Type) := {
  A_selective_presemiring_eqv           : A_eqv S 
; A_selective_presemiring_plus          : binary_op S 
; A_selective_presemiring_times         : binary_op S 
; A_selective_presemiring_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_presemiring_eqv) A_selective_presemiring_plus
; A_selective_presemiring_times_proofs  : sg_proofs S   (A_eqv_eq S A_selective_presemiring_eqv) A_selective_presemiring_times
; A_selective_presemiring_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_selective_presemiring_eqv) A_selective_presemiring_plus A_selective_presemiring_times
; A_selective_presemiring_proofs        : semiring_proofs S (A_eqv_eq S A_selective_presemiring_eqv) A_selective_presemiring_plus A_selective_presemiring_times
; A_selective_presemiring_ast           : cas_bs_ast
}.



Record A_selective_semiring (S : Type) := {
  A_selective_semiring_eqv           : A_eqv S 
; A_selective_semiring_plus          : binary_op S 
; A_selective_semiring_times         : binary_op S 
; A_selective_semiring_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_plus
; A_selective_semiring_times_proofs  : sg_proofs S   (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_times
; A_selective_semiring_id_ann_proofs : pid_is_tann_proofs S (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_plus A_selective_semiring_times
; A_selective_semiring_proofs        : semiring_proofs S (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_plus A_selective_semiring_times
; A_selective_semiring_ast           : cas_bs_ast
}.

Record A_selective_pre_dioid (S : Type) := {
  A_selective_pre_dioid_eqv           : A_eqv S 
; A_selective_pre_dioid_plus          : binary_op S 
; A_selective_pre_dioid_times         : binary_op S 
; A_selective_pre_dioid_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_pre_dioid_eqv) A_selective_pre_dioid_plus
; A_selective_pre_dioid_times_proofs  : sg_proofs S   (A_eqv_eq S A_selective_pre_dioid_eqv) A_selective_pre_dioid_times
; A_selective_pre_dioid_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_selective_pre_dioid_eqv) A_selective_pre_dioid_plus A_selective_pre_dioid_times
; A_selective_pre_dioid_proofs        : dioid_proofs S (A_eqv_eq S A_selective_pre_dioid_eqv) A_selective_pre_dioid_plus A_selective_pre_dioid_times
; A_selective_pre_dioid_ast           : cas_bs_ast
}.

Record A_selective_pre_dioid_with_zero (S : Type) := {
  A_selective_pre_dioid_with_zero_eqv           : A_eqv S 
; A_selective_pre_dioid_with_zero_plus          : binary_op S 
; A_selective_pre_dioid_with_zero_times         : binary_op S 
; A_selective_pre_dioid_with_zero_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_pre_dioid_with_zero_eqv) A_selective_pre_dioid_with_zero_plus
; A_selective_pre_dioid_with_zero_times_proofs  : sg_proofs S   (A_eqv_eq S A_selective_pre_dioid_with_zero_eqv) A_selective_pre_dioid_with_zero_times
; A_selective_pre_dioid_with_zero_id_ann_proofs : pid_is_tann_proofs S (A_eqv_eq S A_selective_pre_dioid_with_zero_eqv) A_selective_pre_dioid_with_zero_plus A_selective_pre_dioid_with_zero_times
; A_selective_pre_dioid_with_zero_proofs        : dioid_proofs S (A_eqv_eq S A_selective_pre_dioid_with_zero_eqv) A_selective_pre_dioid_with_zero_plus A_selective_pre_dioid_with_zero_times
; A_selective_pre_dioid_with_zero_ast           : cas_bs_ast
}.


Record A_selective_pre_dioid_with_one (S : Type) := {
  A_selective_pre_dioid_with_one_eqv           : A_eqv S 
; A_selective_pre_dioid_with_one_plus          : binary_op S 
; A_selective_pre_dioid_with_one_times         : binary_op S 
; A_selective_pre_dioid_with_one_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_pre_dioid_with_one_eqv) A_selective_pre_dioid_with_one_plus
; A_selective_pre_dioid_with_one_times_proofs  : sg_proofs S   (A_eqv_eq S A_selective_pre_dioid_with_one_eqv) A_selective_pre_dioid_with_one_times
; A_selective_pre_dioid_with_one_id_ann_proofs : pann_is_tid_proofs S (A_eqv_eq S A_selective_pre_dioid_with_one_eqv) A_selective_pre_dioid_with_one_plus A_selective_pre_dioid_with_one_times
; A_selective_pre_dioid_with_one_proofs        : dioid_proofs S (A_eqv_eq S A_selective_pre_dioid_with_one_eqv) A_selective_pre_dioid_with_one_plus A_selective_pre_dioid_with_one_times
; A_selective_pre_dioid_with_one_ast           : cas_bs_ast
}.


Record A_selective_dioid (S : Type) := {
  A_selective_dioid_eqv           : A_eqv S 
; A_selective_dioid_plus          : binary_op S 
; A_selective_dioid_times         : binary_op S 
; A_selective_dioid_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_plus
; A_selective_dioid_times_proofs  : sg_proofs S   (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_times
; A_selective_dioid_id_ann_proofs : dually_bounded_proofs S (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_plus A_selective_dioid_times
; A_selective_dioid_proofs        : dioid_proofs S (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_plus A_selective_dioid_times
; A_selective_dioid_ast           : cas_bs_ast
}.

Record A_selective_cancellative_pre_dioid (S : Type) := {
  A_selective_cancellative_pre_dioid_eqv           : A_eqv S 
; A_selective_cancellative_pre_dioid_plus          : binary_op S 
; A_selective_cancellative_pre_dioid_times         : binary_op S 
; A_selective_cancellative_pre_dioid_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_eqv) A_selective_cancellative_pre_dioid_plus
; A_selective_cancellative_pre_dioid_times_proofs  : sg_CK_proofs S   (A_eqv_eq S A_selective_cancellative_pre_dioid_eqv) A_selective_cancellative_pre_dioid_times
; A_selective_cancellative_pre_dioid_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_eqv) A_selective_cancellative_pre_dioid_plus A_selective_cancellative_pre_dioid_times
; A_selective_cancellative_pre_dioid_proofs        : dioid_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_eqv) A_selective_cancellative_pre_dioid_plus A_selective_cancellative_pre_dioid_times
; A_selective_cancellative_pre_dioid_ast           : cas_bs_ast
}.

Record A_selective_cancellative_pre_dioid_with_zero (S : Type) := {
  A_selective_cancellative_pre_dioid_with_zero_eqv           : A_eqv S 
; A_selective_cancellative_pre_dioid_with_zero_plus          : binary_op S 
; A_selective_cancellative_pre_dioid_with_zero_times         : binary_op S 
; A_selective_cancellative_pre_dioid_with_zero_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_with_zero_eqv) A_selective_cancellative_pre_dioid_with_zero_plus
; A_selective_cancellative_pre_dioid_with_zero_times_proofs  : sg_CK_proofs S   (A_eqv_eq S A_selective_cancellative_pre_dioid_with_zero_eqv) A_selective_cancellative_pre_dioid_with_zero_times
; A_selective_cancellative_pre_dioid_with_zero_id_ann_proofs : pid_is_tann_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_with_zero_eqv) A_selective_cancellative_pre_dioid_with_zero_plus A_selective_cancellative_pre_dioid_with_zero_times
; A_selective_cancellative_pre_dioid_with_zero_proofs        : dioid_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_with_zero_eqv) A_selective_cancellative_pre_dioid_with_zero_plus A_selective_cancellative_pre_dioid_with_zero_times
; A_selective_cancellative_pre_dioid_with_zero_ast           : cas_bs_ast
}.

Record A_selective_cancellative_pre_dioid_with_one (S : Type) := {
  A_selective_cancellative_pre_dioid_with_one_eqv           : A_eqv S 
; A_selective_cancellative_pre_dioid_with_one_plus          : binary_op S 
; A_selective_cancellative_pre_dioid_with_one_times         : binary_op S 
; A_selective_cancellative_pre_dioid_with_one_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_with_one_eqv) A_selective_cancellative_pre_dioid_with_one_plus
; A_selective_cancellative_pre_dioid_with_one_times_proofs  : sg_CK_proofs S   (A_eqv_eq S A_selective_cancellative_pre_dioid_with_one_eqv) A_selective_cancellative_pre_dioid_with_one_times
; A_selective_cancellative_pre_dioid_with_one_id_ann_proofs : pann_is_tid_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_with_one_eqv) A_selective_cancellative_pre_dioid_with_one_plus A_selective_cancellative_pre_dioid_with_one_times
; A_selective_cancellative_pre_dioid_with_one_proofs        : dioid_proofs S (A_eqv_eq S A_selective_cancellative_pre_dioid_with_one_eqv) A_selective_cancellative_pre_dioid_with_one_plus A_selective_cancellative_pre_dioid_with_one_times
; A_selective_cancellative_pre_dioid_with_one_ast           : cas_bs_ast
}.

Record A_selective_cancellative_dioid (S : Type) := {
  A_selective_cancellative_dioid_eqv           : A_eqv S 
; A_selective_cancellative_dioid_plus          : binary_op S 
; A_selective_cancellative_dioid_times         : binary_op S 
; A_selective_cancellative_dioid_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_cancellative_dioid_eqv) A_selective_cancellative_dioid_plus
; A_selective_cancellative_dioid_times_proofs  : sg_CK_proofs S   (A_eqv_eq S A_selective_cancellative_dioid_eqv) A_selective_cancellative_dioid_times
; A_selective_cancellative_dioid_id_ann_proofs : dually_bounded_proofs S (A_eqv_eq S A_selective_cancellative_dioid_eqv) A_selective_cancellative_dioid_plus A_selective_cancellative_dioid_times
; A_selective_cancellative_dioid_proofs        : dioid_proofs S (A_eqv_eq S A_selective_cancellative_dioid_eqv) A_selective_cancellative_dioid_plus A_selective_cancellative_dioid_times
; A_selective_cancellative_dioid_ast           : cas_bs_ast
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
; A_selective_distributive_prelattice_ast         : cas_bs_ast
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
; A_selective_distributive_prelattice_with_zero_ast         : cas_bs_ast
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
; A_selective_distributive_prelattice_with_one_ast         : cas_bs_ast
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
; A_selective_distributive_lattice_ast         : cas_bs_ast
}.




End ACAS.

Section AMCAS.

Inductive A_bs_mcas S : Type :=
| A_BS_Error : list string             -> A_bs_mcas S
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



(*            

Need to add idempotent_semiring, idempotent_pre_semiring ? 


        ---------------bs
        |               |
      2 |             1 |
        |               |             5
   pre_semiring       bs_CI <---------------- pre_lattice 
      3 |             |                       /15     |
     semiring       7 |                      /        |
        |             |                lattice         | 13
      4 |       pre_dioid                |             |
        |      8 /  \ 9                  | 6           | 
pre_dioid_with_zero  pre_dioid_with_one  |    ---- distributive_prelattice
              10 \   / 11                |   /
                 dioid                   |  / 14 
                     |                   | /
                  12 |                   / 
                     distributive_lattice




                              bs 
                              | 
                              | 1
                              |
                            bs_CS 
                              |
                              | 2 
                              |
           ----------selective_presemiring
           |                  | 
         3 |                  | 5
           |                  | 
selective_semiring      selective_pre_dioid --------------------------
        |                    /\                                       | 
      4 |                   /  \                                      |
        |                6 /    \ 7                                   | 10
selective_pre_dioid_with_zero  selective_pre_dioid_with_one           | 
                        8 \     / 9                                   |
                           \   /                                      | 
             ---------selective_dioid                                 | 
             |                                                        | 
          11 |                                          A_selective_distributive_prelattice
             |                                        12 /                               \ 13
             |               selective_distributive_prelattice_with_zero      selective_distributive_prelattice_with_one
             |                                        14 \                              / 15 
             -------------------------------------------  selective_distributive_lattice




                                   | 
                                   | 5
                                   |
                          selective_pre_dioid
                        6 /        |        \ 7 
selective_pre_dioid_with_zero    16|       selective_pre_dioid_with_one
    |                              |                           | 
 17 |                 selective_cancellative_pre_dioid         | 18
    |              19 /                               \ 20     |
selective_cancellative_pre_dioid_with_zero     selective_cancellative_pre_dioid_with_one
                    21  \                              / 22
                          selective_cancellative_dioid





selective_pre_dioid_with_zero                     selective_pre_dioid_with_one          
             |                                              | 
             | 23                                           | 24 
             |                                              | 
selective_distributive_prelattice_with_zero    selective_distributive_prelattice_with_one


 *)
Definition A_bs_classify_selective_distributive_lattice (S : Type) (B : A_selective_distributive_lattice S) : A_bs_mcas S :=
  A_BS_selective_distributive_lattice _ B. 

Definition A_bs_classify_selective_distributive_prelattice_with_one (S : Type) (B : A_selective_distributive_prelattice_with_one S) : A_bs_mcas S :=
  A_BS_selective_distributive_prelattice_with_one _ B. 

Definition A_bs_classify_selective_distributive_prelattice_with_zero (S : Type) (B : A_selective_distributive_prelattice_with_zero S) : A_bs_mcas S :=
  A_BS_selective_distributive_prelattice_with_zero _ B. 

Definition A_bs_classify_selective_distributive_prelattice (S : Type) (B : A_selective_distributive_prelattice S) : A_bs_mcas S :=
  A_BS_selective_distributive_prelattice _ B. 

Definition A_bs_classify_distributive_lattice (S : Type) (B : A_distributive_lattice S) : A_bs_mcas S :=
  A_BS_distributive_lattice _ B. 

Definition A_bs_classify_lattice  (S : Type) (B : A_lattice  S) : A_bs_mcas S :=
  A_BS_lattice  _ B. 

Definition A_bs_classify_distributive_prelattice (S : Type) (B : A_distributive_prelattice S) : A_bs_mcas S :=
  A_BS_distributive_prelattice _ B. 

Definition A_bs_classify_prelattice (S : Type) (B : A_prelattice S) : A_bs_mcas S :=
  A_BS_prelattice _ B. 

Definition A_bs_classify_selective_cancellative_dioid (S : Type) (B : A_selective_cancellative_dioid S) : A_bs_mcas S :=
  A_BS_selective_cancellative_dioid _ B. 

Definition A_bs_classify_selective_cancellative_pre_dioid_with_one (S : Type) (B : A_selective_cancellative_pre_dioid_with_one S) : A_bs_mcas S :=
  A_BS_selective_cancellative_pre_dioid_with_one _ B. 

Definition A_bs_classify_selective_cancellative_pre_dioid_with_zero (S : Type) (B : A_selective_cancellative_pre_dioid_with_zero S) : A_bs_mcas S :=
  A_BS_selective_cancellative_pre_dioid_with_zero _ B. 

Definition A_bs_classify_selective_cancellative_pre_dioid (S : Type) (B : A_selective_cancellative_pre_dioid S) : A_bs_mcas S :=
  A_BS_selective_cancellative_pre_dioid _ B. 

Definition A_bs_classify_selective_dioid (S : Type) (B : A_selective_dioid S) : A_bs_mcas S :=
  A_BS_selective_dioid _ B. 

Definition A_bs_classify_selective_pre_dioid_with_one (S : Type) (B : A_selective_pre_dioid_with_one S) : A_bs_mcas S :=
  A_BS_selective_pre_dioid_with_one _ B. 

Definition A_bs_classify_selective_pre_dioid_with_zero (S : Type) (B : A_selective_pre_dioid_with_zero S) : A_bs_mcas S :=
  A_BS_selective_pre_dioid_with_zero _ B. 

(*
  selective_pre_dioid 
  => selective_dioid 
  => selective_pre_dioid_with_one
  => selective_pre_dioid_with_zero 
*) 
Definition A_bs_classify_selective_pre_dioid (S : Type) (B : A_selective_pre_dioid S) : A_bs_mcas S :=

let eqv     := A_selective_pre_dioid_eqv _ B in
let plus    := A_selective_pre_dioid_plus _ B in
let times   := A_selective_pre_dioid_times _ B in    
let plusP   := A_selective_pre_dioid_plus_proofs _ B in
let timesP  := A_selective_pre_dioid_times_proofs _ B in
let id_annP := A_selective_pre_dioid_id_ann_proofs _ B in
let bsP     := A_selective_pre_dioid_proofs _ B in
let ast     := A_selective_pre_dioid_ast _ B in
match A_id_ann_plus_times_d _ _ _ _ id_annP,
      A_id_ann_times_plus_d _ _ _ _ id_annP
with
|  Id_Ann_Proof_Equal _ _ _ _ P1, Id_Ann_Proof_Equal _ _ _ _ P2 => A_BS_selective_dioid _
   {|                                                               
      A_selective_dioid_eqv           := eqv 
    ; A_selective_dioid_plus          := plus
    ; A_selective_dioid_times         := times
    ; A_selective_dioid_plus_proofs   := plusP 
    ; A_selective_dioid_times_proofs  := timesP 
    ; A_selective_dioid_id_ann_proofs :=
        {|
           A_bounded_plus_id_is_times_ann := P1
         ; A_bounded_times_id_is_plus_ann := P2
        |}
    ; A_selective_dioid_proofs        := bsP 
    ; A_selective_dioid_ast           := ast 
   |}   
|  Id_Ann_Proof_Equal _ _ _ _ P1, P2 => A_BS_selective_pre_dioid_with_zero _
   {|                                                               
      A_selective_pre_dioid_with_zero_eqv           := eqv 
    ; A_selective_pre_dioid_with_zero_plus          := plus
    ; A_selective_pre_dioid_with_zero_times         := times
    ; A_selective_pre_dioid_with_zero_plus_proofs   := plusP 
    ; A_selective_pre_dioid_with_zero_times_proofs  := timesP 
    ; A_selective_pre_dioid_with_zero_id_ann_proofs :=
        {|
           A_pid_is_tann_plus_times   := P1
         ; A_pid_is_tann_times_plus_d := P2
        |}
    ; A_selective_pre_dioid_with_zero_proofs        := bsP 
    ; A_selective_pre_dioid_with_zero_ast           := ast 
   |}   
|  P1, Id_Ann_Proof_Equal _ _ _ _ P2 => A_BS_selective_pre_dioid_with_one _
   {|                                                               
      A_selective_pre_dioid_with_one_eqv           := eqv 
    ; A_selective_pre_dioid_with_one_plus          := plus
    ; A_selective_pre_dioid_with_one_times         := times
    ; A_selective_pre_dioid_with_one_plus_proofs   := plusP 
    ; A_selective_pre_dioid_with_one_times_proofs  := timesP 
    ; A_selective_pre_dioid_with_one_id_ann_proofs :=
        {|
           A_pann_is_tid_plus_times_d   := P1
         ; A_pann_is_tid_times_plus := P2
        |}
    ; A_selective_pre_dioid_with_one_proofs        := bsP 
    ; A_selective_pre_dioid_with_one_ast           := ast 
   |}   
| _, _ => A_BS_selective_pre_dioid _ B
end. 

(* do we want a cancellative dioid? *) 
Definition A_bs_classify_dioid (S : Type) (B : A_dioid S) : A_bs_mcas S :=
  A_BS_dioid _ B. 

(*
  pre_dioid_with_zero
  => dioid
*) 
Definition A_bs_classify_pre_dioid_with_zero (S : Type) (B : A_pre_dioid_with_zero S) : A_bs_mcas S :=
let id_annP := A_pre_dioid_with_zero_id_ann_proofs _ B in
match A_pid_is_tann_times_plus_d _ _ _ _ id_annP with
|  Id_Ann_Proof_Equal _ _ _ _ P2 => A_bs_classify_dioid _ 
   {|                                                               
      A_dioid_eqv           := A_pre_dioid_with_zero_eqv _ B
    ; A_dioid_plus          := A_pre_dioid_with_zero_plus _ B
    ; A_dioid_times         := A_pre_dioid_with_zero_times _ B 
    ; A_dioid_plus_proofs   := A_pre_dioid_with_zero_plus_proofs _ B 
    ; A_dioid_times_proofs  := A_pre_dioid_with_zero_times_proofs _ B 
    ; A_dioid_id_ann_proofs :=
        {|
           A_bounded_plus_id_is_times_ann := A_pid_is_tann_plus_times  _ _ _ _ id_annP
         ; A_bounded_times_id_is_plus_ann := P2
        |}
    ; A_dioid_proofs        := A_pre_dioid_with_zero_proofs _ B 
    ; A_dioid_ast           := A_pre_dioid_with_zero_ast _ B 
   |}   
| _ => A_BS_pre_dioid_with_zero _ B
end. 

(*
  pre_dioid_with_one 
  => dioid
*) 
Definition A_bs_classify_pre_dioid_with_one (S : Type) (B : A_pre_dioid_with_one S) : A_bs_mcas S :=
let id_annP := A_pre_dioid_with_one_id_ann_proofs _ B in
match A_pann_is_tid_plus_times_d _ _ _ _ id_annP with
|  Id_Ann_Proof_Equal _ _ _ _ P1 => A_bs_classify_dioid _ 
   {|                                                               
      A_dioid_eqv           := A_pre_dioid_with_one_eqv _ B
    ; A_dioid_plus          := A_pre_dioid_with_one_plus _ B
    ; A_dioid_times         := A_pre_dioid_with_one_times _ B 
    ; A_dioid_plus_proofs   := A_pre_dioid_with_one_plus_proofs _ B 
    ; A_dioid_times_proofs  := A_pre_dioid_with_one_times_proofs _ B 
    ; A_dioid_id_ann_proofs :=
        {|
           A_bounded_plus_id_is_times_ann := P1 
         ; A_bounded_times_id_is_plus_ann := A_pann_is_tid_times_plus _ _ _ _ id_annP
        |}
    ; A_dioid_proofs        := A_pre_dioid_with_one_proofs _ B 
    ; A_dioid_ast           := A_pre_dioid_with_one_ast _ B 
   |}   
| _ => A_BS_pre_dioid_with_one _ B
end. 

(* 
   pre_dioid
   => dioid
   => pre_dioid_with_zero
   => pre_dioid_with_one

*) 
Definition A_bs_classify_pre_dioid (S : Type) (B : A_pre_dioid S) : A_bs_mcas S :=
let eqv     := A_pre_dioid_eqv _ B in
let plus    := A_pre_dioid_plus _ B in
let times   := A_pre_dioid_times _ B in    
let plusP   := A_pre_dioid_plus_proofs _ B in
let timesP  := A_pre_dioid_times_proofs _ B in
let id_annP := A_pre_dioid_id_ann_proofs _ B in
let bsP     := A_pre_dioid_proofs _ B in
let ast     := A_pre_dioid_ast _ B in
match A_id_ann_plus_times_d _ _ _ _ id_annP,
      A_id_ann_times_plus_d _ _ _ _ id_annP
with
|  Id_Ann_Proof_Equal _ _ _ _ P1, Id_Ann_Proof_Equal _ _ _ _ P2 => A_BS_dioid _
   {|                                                               
      A_dioid_eqv           := eqv 
    ; A_dioid_plus          := plus
    ; A_dioid_times         := times
    ; A_dioid_plus_proofs   := plusP 
    ; A_dioid_times_proofs  := timesP 
    ; A_dioid_id_ann_proofs :=
        {|
           A_bounded_plus_id_is_times_ann := P1
         ; A_bounded_times_id_is_plus_ann := P2
        |}
    ; A_dioid_proofs        := bsP 
    ; A_dioid_ast           := ast 
   |}   
|  Id_Ann_Proof_Equal _ _ _ _ P1, P2 => A_BS_pre_dioid_with_zero _
   {|                                                               
      A_pre_dioid_with_zero_eqv           := eqv 
    ; A_pre_dioid_with_zero_plus          := plus
    ; A_pre_dioid_with_zero_times         := times
    ; A_pre_dioid_with_zero_plus_proofs   := plusP 
    ; A_pre_dioid_with_zero_times_proofs  := timesP 
    ; A_pre_dioid_with_zero_id_ann_proofs :=
        {|
           A_pid_is_tann_plus_times   := P1
         ; A_pid_is_tann_times_plus_d := P2
        |}
    ; A_pre_dioid_with_zero_proofs        := bsP 
    ; A_pre_dioid_with_zero_ast           := ast 
   |}   
|  P1, Id_Ann_Proof_Equal _ _ _ _ P2 => A_BS_pre_dioid_with_one _
   {|                                                               
      A_pre_dioid_with_one_eqv           := eqv 
    ; A_pre_dioid_with_one_plus          := plus
    ; A_pre_dioid_with_one_times         := times
    ; A_pre_dioid_with_one_plus_proofs   := plusP 
    ; A_pre_dioid_with_one_times_proofs  := timesP 
    ; A_pre_dioid_with_one_id_ann_proofs :=
        {|
           A_pann_is_tid_plus_times_d   := P1
         ; A_pann_is_tid_times_plus := P2
        |}
    ; A_pre_dioid_with_one_proofs        := bsP 
    ; A_pre_dioid_with_one_ast           := ast 
   |}   
| _, _ => A_BS_pre_dioid _ B
end. 
  

(*
    selective_semiring
     => selective_pre_dioid_with_zero
 *)
Definition A_bs_classify_selective_semiring (S : Type) (B : A_selective_semiring S) : A_bs_mcas S :=
let P := A_selective_semiring_proofs _ B in
match A_semiring_left_left_absorptive_d _ _ _ _ P,
      A_semiring_left_right_absorptive_d _ _ _ _ P
with
|  inl lla, inl lra => A_bs_classify_selective_pre_dioid_with_zero _ 
   {|                                                               
      A_selective_pre_dioid_with_zero_eqv           := A_selective_semiring_eqv _ B
    ; A_selective_pre_dioid_with_zero_plus          := A_selective_semiring_plus _ B
    ; A_selective_pre_dioid_with_zero_times         := A_selective_semiring_times _ B 
    ; A_selective_pre_dioid_with_zero_plus_proofs   := A_selective_semiring_plus_proofs _ B 
    ; A_selective_pre_dioid_with_zero_times_proofs  := A_selective_semiring_times_proofs _ B 
    ; A_selective_pre_dioid_with_zero_id_ann_proofs := A_selective_semiring_id_ann_proofs _ B
    ; A_selective_pre_dioid_with_zero_proofs        :=
                {|
                    A_dioid_left_distributive     := A_semiring_left_distributive _ _ _ _ P
                  ; A_dioid_right_distributive    := A_semiring_right_distributive _ _ _ _ P
                  ; A_dioid_left_left_absorptive  := lla
                  ; A_dioid_left_right_absorptive := lra              
                 |} 
    ; A_selective_pre_dioid_with_zero_ast           := A_selective_semiring_ast _ B 
   |}   
| _, _ => A_BS_selective_semiring _ B
end. 


(*
   selective_presemiring
   => selective_semiring
   => selective_pre_dioid
*) 
Definition A_bs_classify_selective_presemiring (S : Type) (B : A_selective_presemiring S) : A_bs_mcas S :=
let eqv     := A_selective_presemiring_eqv _ B in
let plus    := A_selective_presemiring_plus _ B in
let times   := A_selective_presemiring_times _ B in    
let plusP   := A_selective_presemiring_plus_proofs _ B in
let timesP  := A_selective_presemiring_times_proofs _ B in
let id_annP := A_selective_presemiring_id_ann_proofs _ B in
let bsP     := A_selective_presemiring_proofs _ B in
let ast     := A_selective_presemiring_ast _ B in
match A_semiring_left_left_absorptive_d _ _ _ _ bsP,
      A_semiring_left_right_absorptive_d _ _ _ _ bsP
with
| inl lla, inl lra => A_bs_classify_selective_pre_dioid _
       {|                                                         
           A_selective_pre_dioid_eqv           := eqv
         ; A_selective_pre_dioid_plus          := plus
         ; A_selective_pre_dioid_times         := times
         ; A_selective_pre_dioid_plus_proofs   := plusP
         ; A_selective_pre_dioid_times_proofs  := timesP
         ; A_selective_pre_dioid_id_ann_proofs := id_annP
         ; A_selective_pre_dioid_proofs        :=
                {|
                    A_dioid_left_distributive     := A_semiring_left_distributive _ _ _ _ bsP
                  ; A_dioid_right_distributive    := A_semiring_right_distributive _ _ _ _ bsP
                  ; A_dioid_left_left_absorptive  := lla
                  ; A_dioid_left_right_absorptive := lra              
                 |} 
         ; A_selective_pre_dioid_ast           := ast 
       |}         
| _, _ =>
  match A_id_ann_plus_times_d _ _ _ _ id_annP with
  | Id_Ann_Proof_Equal _ _ _ _ P => A_bs_classify_selective_semiring _
          {| 
              A_selective_semiring_eqv           := eqv
            ; A_selective_semiring_plus          := plus
            ; A_selective_semiring_times         := times
            ; A_selective_semiring_plus_proofs   := plusP
            ; A_selective_semiring_times_proofs  := timesP
            ; A_selective_semiring_id_ann_proofs :=
               {|
                   A_pid_is_tann_plus_times   := P 
                 ; A_pid_is_tann_times_plus_d := A_id_ann_times_plus_d  _ _ _ _ id_annP 
              |}
            ; A_selective_semiring_proofs        := bsP 
            ; A_selective_semiring_ast           := ast 
           |}                               
  | _ => A_BS_selective_presemiring _ B
  end
end. 


(* 
   semiring
   => selective_semiring 
   => pre_dioid_with_zero 
 *)
Definition A_bs_classify_semiring (S : Type) (B : A_semiring S) : A_bs_mcas S :=
let plusP   := A_semiring_plus_proofs _ B in
let srP     := A_semiring_proofs _ B in  
match A_sg_C_selective_d _ _ _ plusP with
| inl selS => A_bs_classify_selective_semiring _
          {|
              A_selective_semiring_eqv           := A_semiring_eqv _ B 
            ; A_selective_semiring_plus          := A_semiring_plus _ B 
            ; A_selective_semiring_times         := A_semiring_times _ B 
            ; A_selective_semiring_plus_proofs   :=
                {|
                    A_sg_CS_associative := A_sg_C_associative _ _ _ plusP
                  ; A_sg_CS_congruence  := A_sg_C_congruence _ _ _ plusP
                  ; A_sg_CS_commutative := A_sg_C_commutative _ _ _ plusP
                  ; A_sg_CS_selective   := selS 
                |}
            ; A_selective_semiring_times_proofs  := A_semiring_times_proofs _ B
            ; A_selective_semiring_id_ann_proofs := A_semiring_id_ann_proofs _ B 
            ; A_selective_semiring_proofs        := A_semiring_proofs _ B 
            ; A_selective_semiring_ast           := A_semiring_ast _ B 
          |}                          
| inr nselS =>
  match A_sg_C_idempotent_d _ _ _ plusP,
        A_semiring_left_left_absorptive_d _ _ _ _ srP,
        A_semiring_left_right_absorptive_d _ _ _ _ srP
  with
  | inl idemS, inl lla, inl lra => A_bs_classify_pre_dioid_with_zero _
          {|
              A_pre_dioid_with_zero_eqv           := A_semiring_eqv _ B 
            ; A_pre_dioid_with_zero_plus          := A_semiring_plus _ B 
            ; A_pre_dioid_with_zero_times         := A_semiring_times _ B 
            ; A_pre_dioid_with_zero_plus_proofs   :=
                {|
                    A_sg_CI_associative   := A_sg_C_associative _ _ _ plusP
                  ; A_sg_CI_congruence    := A_sg_C_congruence _ _ _ plusP
                  ; A_sg_CI_commutative   := A_sg_C_commutative _ _ _ plusP
                  ; A_sg_CI_idempotent    := idemS 
                  ; A_sg_CI_not_selective := nselS 
                |}
            ; A_pre_dioid_with_zero_times_proofs  := A_semiring_times_proofs _ B
            ; A_pre_dioid_with_zero_id_ann_proofs := A_semiring_id_ann_proofs _ B
            ; A_pre_dioid_with_zero_proofs        :=
                {|
                    A_dioid_left_distributive     := A_semiring_left_distributive _ _ _ _ srP
                  ; A_dioid_right_distributive    := A_semiring_right_distributive _ _ _ _ srP
                  ; A_dioid_left_left_absorptive  := lla 
                  ; A_dioid_left_right_absorptive := lra                   
                 |}
            ; A_pre_dioid_with_zero_ast           := A_semiring_ast _ B 
          |}      
  | _, _, _  => A_BS_semiring _ B    
  end 
end. 

(* 
   presemiring
   => selective_presemiring 
   => semiring 
   => pre dioid (link not in diagram!)
 *)
Definition A_bs_classify_presemiring (S : Type) (B : A_presemiring S) : A_bs_mcas S :=
let plusP   := A_presemiring_plus_proofs _ B in
let srP     := A_presemiring_proofs _ B in    
match A_sg_C_selective_d _ _ _ plusP with
| inl selS => A_bs_classify_selective_presemiring _
          {|
              A_selective_presemiring_eqv           := A_presemiring_eqv _ B 
            ; A_selective_presemiring_plus          := A_presemiring_plus _ B 
            ; A_selective_presemiring_times         := A_presemiring_times _ B 
            ; A_selective_presemiring_plus_proofs   :=
                {|
                    A_sg_CS_associative := A_sg_C_associative _ _ _ plusP
                  ; A_sg_CS_congruence  := A_sg_C_congruence _ _ _ plusP
                  ; A_sg_CS_commutative := A_sg_C_commutative _ _ _ plusP
                  ; A_sg_CS_selective   := selS 
                |}
            ; A_selective_presemiring_times_proofs  := A_presemiring_times_proofs _ B
            ; A_selective_presemiring_id_ann_proofs := A_presemiring_id_ann_proofs _ B 
            ; A_selective_presemiring_proofs        := A_presemiring_proofs _ B 
            ; A_selective_presemiring_ast           := A_presemiring_ast _ B 
          |}                          
| inr nselS =>
  match A_id_ann_plus_times_d _ _ _ _ (A_presemiring_id_ann_proofs _ B) with
  | Id_Ann_Proof_Equal _ _ _ _ P => A_bs_classify_semiring _
          {|
              A_semiring_eqv           := A_presemiring_eqv _ B 
            ; A_semiring_plus          := A_presemiring_plus _ B 
            ; A_semiring_times         := A_presemiring_times _ B 
            ; A_semiring_plus_proofs   := A_presemiring_plus_proofs _ B 
            ; A_semiring_times_proofs  := A_presemiring_times_proofs _ B
            ; A_semiring_id_ann_proofs :=
                {|
                   A_pid_is_tann_plus_times   := P
                 ; A_pid_is_tann_times_plus_d := A_id_ann_times_plus_d _ _ _ _ (A_presemiring_id_ann_proofs _ B)
                |}                
            ; A_semiring_proofs        := A_presemiring_proofs _ B 
            ; A_semiring_ast           := A_presemiring_ast _ B 
          |}      
  | _ =>
    match A_sg_C_idempotent_d _ _ _ plusP,
          A_semiring_left_left_absorptive_d _ _ _ _ srP,
          A_semiring_left_right_absorptive_d _ _ _ _ srP
    with
    | inl idemS, inl lla, inl lra => A_bs_classify_pre_dioid _
         {|
              A_pre_dioid_eqv           := A_presemiring_eqv _ B 
            ; A_pre_dioid_plus          := A_presemiring_plus _ B 
            ; A_pre_dioid_times         := A_presemiring_times _ B 
            ; A_pre_dioid_plus_proofs   :=
                {|
                    A_sg_CI_associative   := A_sg_C_associative _ _ _ plusP
                  ; A_sg_CI_congruence    := A_sg_C_congruence _ _ _ plusP
                  ; A_sg_CI_commutative   := A_sg_C_commutative _ _ _ plusP
                  ; A_sg_CI_idempotent    := idemS 
                  ; A_sg_CI_not_selective := nselS 
                |}
            ; A_pre_dioid_times_proofs  := A_presemiring_times_proofs _ B
            ; A_pre_dioid_id_ann_proofs := A_presemiring_id_ann_proofs _ B
            ; A_pre_dioid_proofs        :=
                {|
                    A_dioid_left_distributive     := A_semiring_left_distributive _ _ _ _ srP
                  ; A_dioid_right_distributive    := A_semiring_right_distributive _ _ _ _ srP
                  ; A_dioid_left_left_absorptive  := lla 
                  ; A_dioid_left_right_absorptive := lra                   
                 |}
            ; A_pre_dioid_ast           := A_presemiring_ast _ B 
          |}      
    | _, _, _ =>  A_BS_presemiring _ B
    end
  end 
end. 
  

(*
 bs_CS
 => selective_presemiring 
*) 
Definition A_bs_classify_bs_CS (S : Type) (B : A_bs_CS S) : A_bs_mcas S :=
let eqv     := A_bs_CS_eqv _ B in
let plus    := A_bs_CS_plus _ B in
let times   := A_bs_CS_times _ B in    
let plusP   := A_bs_CS_plus_proofs _ B in
let timesP  := A_bs_CS_times_proofs _ B in
let id_annP := A_bs_CS_id_ann_proofs _ B in
let bsP     := A_bs_CS_proofs _ B in
let ast     := A_bs_CS_ast _ B in
match A_bs_left_distributive_d _ _ _ _ bsP,
      A_bs_right_distributive_d _ _ _ _ bsP
with
| inl ld, inl rd => A_bs_classify_selective_presemiring _
          {|
              A_selective_presemiring_eqv           := eqv
            ; A_selective_presemiring_plus           := plus
            ; A_selective_presemiring_times         := times
            ; A_selective_presemiring_plus_proofs   := plusP
            ; A_selective_presemiring_times_proofs  := timesP
            ; A_selective_presemiring_id_ann_proofs := id_annP 
            ; A_selective_presemiring_proofs        :=
                {|
                    A_semiring_left_distributive       := ld
                  ; A_semiring_right_distributive      := rd 
                  ; A_semiring_left_left_absorptive_d  := A_bs_left_left_absorptive_d _ _ _ _ bsP
                  ; A_semiring_left_right_absorptive_d := A_bs_left_right_absorptive_d _ _ _ _ bsP
                 |} 
            ; A_selective_presemiring_ast           := ast 
          |}                          
| _, _ => A_BS_bs_CS _ B 
end. 

(*
   classify 
   bs_CI
   --> pre_dioid
   --> pre_lattice (* not yet, need dual properties in A_bs! *) 
*) 


Definition A_bs_classify_bs_CI (S : Type) (B : A_bs_CI S) : A_bs_mcas S :=
let eqv     := A_bs_CI_eqv _ B in
let plus    := A_bs_CI_plus _ B in
let times   := A_bs_CI_times _ B in    
let plusP   := A_bs_CI_plus_proofs _ B in
let timesP  := A_bs_CI_times_proofs _ B in
let id_annP := A_bs_CI_id_ann_proofs _ B in
let bsP     := A_bs_CI_proofs _ B in
let ast     := A_bs_CI_ast _ B in
match A_bs_left_distributive_d _ _ _ _ bsP,
      A_bs_right_distributive_d _ _ _ _ bsP,
      A_bs_left_left_absorptive_d _ _ _ _ bsP,       
      A_bs_left_right_absorptive_d _ _ _ _ bsP
with
| inl ld, inl rd, inl lla, inl lra => A_bs_classify_pre_dioid _
          {|
              A_pre_dioid_eqv           := eqv
            ; A_pre_dioid_plus          := plus
            ; A_pre_dioid_times         := times
            ; A_pre_dioid_plus_proofs   := plusP
            ; A_pre_dioid_times_proofs  := timesP
            ; A_pre_dioid_id_ann_proofs := id_annP 
            ; A_pre_dioid_proofs        :=
                {|
                    A_dioid_left_distributive     := ld
                  ; A_dioid_right_distributive    := rd 
                  ; A_dioid_left_left_absorptive  := lla
                  ; A_dioid_left_right_absorptive := lra              
                 |} 
            ; A_pre_dioid_ast           := ast 
          |}                          
| _, _, _, _ => A_BS_bs_CI _ B 
end. 


(*
   classify 
   bs 
   --> bs_CI
   --> bs_CI
   --> bs_presemiring
   --> bs_selective_presemiring
*) 

Definition A_bs_classify_bs (S : Type) (B : A_bs S) : A_bs_mcas S :=
let eqv     := A_bs_eqv _ B in
let plus    := A_bs_plus _ B in
let times   := A_bs_times _ B in    
let plusP   := A_bs_plus_proofs _ B in
let timesP  := A_bs_times_proofs _ B in
let id_annP := A_bs_id_ann_proofs _ B in
let bsP     := A_bs_proofs _ B in
let ast     := A_bs_ast _ B in
match A_sg_commutative_d _ _ _ plusP with
| inl comm =>
  match A_sg_idempotent_d _ _ _ plusP with
  | inl idem =>
    match A_sg_selective_d _ _ _ plusP with
    | inl sel =>
      let sg_CS_P :=
                  {|
                      A_sg_CS_associative := A_sg_associative _ _ _ plusP 
                    ; A_sg_CS_congruence  := A_sg_congruence _ _ _ plusP 
                    ; A_sg_CS_commutative := comm
                    ; A_sg_CS_selective   := sel
                  |} in           
      match A_bs_left_distributive_d _ _ _ _ bsP with
      | inl ld =>
        match A_bs_right_distributive_d _ _ _ _ bsP with
        | inl rd => A_bs_classify_selective_presemiring _ 
                 {|
                     A_selective_presemiring_eqv           := eqv
                   ; A_selective_presemiring_plus          := plus
                   ; A_selective_presemiring_times         := times 
                   ; A_selective_presemiring_plus_proofs   := sg_CS_P
                   ; A_selective_presemiring_times_proofs  := timesP 
                   ; A_selective_presemiring_id_ann_proofs := id_annP
                   ; A_selective_presemiring_proofs        :=
                       {|
                           A_semiring_left_distributive       := ld  
                         ; A_semiring_right_distributive      := rd 
                         ; A_semiring_left_left_absorptive_d  := A_bs_left_left_absorptive_d _ _ _ _ bsP
                         ; A_semiring_left_right_absorptive_d := A_bs_left_right_absorptive_d _ _ _ _ bsP
                       |}
                   ; A_selective_presemiring_ast           := ast
                  |}
        | inr nrd => A_bs_classify_bs_CS _
                  {|
                      A_bs_CS_eqv           := eqv
                    ; A_bs_CS_plus          := plus 
                    ; A_bs_CS_times         := times 
                    ; A_bs_CS_plus_proofs   := sg_CS_P  
                    ; A_bs_CS_times_proofs  := timesP
                    ; A_bs_CS_id_ann_proofs := id_annP
                    ; A_bs_CS_proofs        := bsP 
                    ; A_bs_CS_ast           := ast 
                  |}                                         
        end 
      | inr nld => A_bs_classify_bs_CS _
                  {|
                      A_bs_CS_eqv           := eqv
                    ; A_bs_CS_plus          := plus 
                    ; A_bs_CS_times         := times 
                    ; A_bs_CS_plus_proofs   := sg_CS_P  
                    ; A_bs_CS_times_proofs  := timesP
                    ; A_bs_CS_id_ann_proofs := id_annP
                    ; A_bs_CS_proofs        := bsP 
                    ; A_bs_CS_ast           := ast 
                  |} 
      end 
    | inr nsel =>
      let sg_CI_P :=
                  {|
                      A_sg_CI_associative   := A_sg_associative _ _ _ plusP 
                    ; A_sg_CI_congruence    := A_sg_congruence _ _ _ plusP 
                    ; A_sg_CI_commutative   := comm
                    ; A_sg_CI_idempotent    := idem
                    ; A_sg_CI_not_selective := nsel
                  |} in           
      match A_bs_left_distributive_d _ _ _ _ bsP with
      | inl ld =>
        match A_bs_right_distributive_d _ _ _ _ bsP with
        | inl rd => A_bs_classify_presemiring _ 
                 {|
                     A_presemiring_eqv           := eqv
                   ; A_presemiring_plus          := plus
                   ; A_presemiring_times         := times 
                   ; A_presemiring_plus_proofs   :=
                        {|
                            A_sg_C_associative  := A_sg_associative _ _ _ plusP 
                          ; A_sg_C_congruence   := A_sg_congruence _ _ _ plusP 
                          ; A_sg_C_commutative  := comm
                          ; A_sg_C_selective_d  := A_sg_selective_d _ _ _ plusP
                          ; A_sg_C_idempotent_d := A_sg_idempotent_d _ _ _ plusP
                          ; A_sg_C_anti_left_d  := A_sg_anti_left_d _ _ _ plusP
                          ; A_sg_C_anti_right_d := A_sg_anti_right_d _ _ _ plusP
                          ; A_sg_C_cancel_d     := A_sg_left_cancel_d _ _ _ plusP
                          ; A_sg_C_constant_d   := A_sg_left_constant_d _ _ _ plusP                                                   
                        |} 
                   ; A_presemiring_times_proofs  := timesP 
                   ; A_presemiring_id_ann_proofs := id_annP
                   ; A_presemiring_proofs        :=
                       {|
                           A_semiring_left_distributive       := ld  
                         ; A_semiring_right_distributive      := rd 
                         ; A_semiring_left_left_absorptive_d  := A_bs_left_left_absorptive_d _ _ _ _ bsP
                         ; A_semiring_left_right_absorptive_d := A_bs_left_right_absorptive_d _ _ _ _ bsP
                       |}
                   ; A_presemiring_ast           := ast
                  |}
        | inr nrd => A_bs_classify_bs_CI _
                  {|
                      A_bs_CI_eqv           := eqv
                    ; A_bs_CI_plus          := plus 
                    ; A_bs_CI_times         := times 
                    ; A_bs_CI_plus_proofs   := sg_CI_P  
                    ; A_bs_CI_times_proofs  := timesP
                    ; A_bs_CI_id_ann_proofs := id_annP
                    ; A_bs_CI_proofs        := bsP 
                    ; A_bs_CI_ast           := ast 
                  |}                                         
        end 
      | inr nld => A_bs_classify_bs_CI _
                  {|
                      A_bs_CI_eqv           := eqv
                    ; A_bs_CI_plus          := plus 
                    ; A_bs_CI_times         := times 
                    ; A_bs_CI_plus_proofs   := sg_CI_P  
                    ; A_bs_CI_times_proofs  := timesP
                    ; A_bs_CI_id_ann_proofs := id_annP
                    ; A_bs_CI_proofs        := bsP 
                    ; A_bs_CI_ast           := ast 
                  |} 
      end 
    end
  | inr nidem =>
    match A_bs_left_distributive_d _ _ _ _ bsP with
    | inl ld =>
      match A_bs_right_distributive_d _ _ _ _ bsP with
      | inl rd => A_bs_classify_presemiring _ 
                  {|
                      A_presemiring_eqv          := eqv  
                    ; A_presemiring_plus         := plus
                    ; A_presemiring_times        := times 
                    ; A_presemiring_plus_proofs  :=
                        {|
                            A_sg_C_associative  := A_sg_associative _ _ _ plusP 
                          ; A_sg_C_congruence   := A_sg_congruence _ _ _ plusP 
                          ; A_sg_C_commutative  := comm
                          ; A_sg_C_selective_d  := A_sg_selective_d _ _ _ plusP
                          ; A_sg_C_idempotent_d := inr nidem
                          ; A_sg_C_anti_left_d  := A_sg_anti_left_d _ _ _ plusP
                          ; A_sg_C_anti_right_d := A_sg_anti_right_d _ _ _ plusP
                          ; A_sg_C_cancel_d     := A_sg_left_cancel_d _ _ _ plusP
                          ; A_sg_C_constant_d   := A_sg_left_constant_d _ _ _ plusP                                                   
                        |} 
                    ; A_presemiring_times_proofs := timesP
                    ; A_presemiring_id_ann_proofs := id_annP                                                      
                    ; A_presemiring_proofs       :=
                        {|                        
                           A_semiring_left_distributive       := ld  
                         ; A_semiring_right_distributive      := rd 
                         ; A_semiring_left_left_absorptive_d  := A_bs_left_left_absorptive_d _ _ _ _ bsP
                         ; A_semiring_left_right_absorptive_d := A_bs_left_right_absorptive_d _ _ _ _ bsP
                        |}                         
                    ; A_presemiring_ast          := ast 
                  |}
      | inr nrd => A_BS_bs _ B                       
      end 
    | inr nld => A_BS_bs _ B               
    end 
  end 
| inr _ => A_BS_bs _ B               
end.

Definition A_bs_classify (S : Type) (A : A_bs_mcas S) : A_bs_mcas S := 
match A with
| A_BS_Error _ _                                         => A
| A_BS_bs _ B                                            => A_bs_classify_bs _ B
| A_BS_bs_CI _ B                                         => A_bs_classify_bs_CI _ B
| A_BS_bs_CS _ B                                         => A_bs_classify_bs_CS _ B
| A_BS_presemiring _ B                                   => A_bs_classify_presemiring _ B
| A_BS_semiring _ B                                      => A_bs_classify_semiring _ B
| A_BS_pre_dioid _ B                                     => A_bs_classify_pre_dioid _ B
| A_BS_pre_dioid_with_one _ B                            => A_bs_classify_pre_dioid_with_one _ B
| A_BS_pre_dioid_with_zero _ B                           => A_bs_classify_pre_dioid_with_zero _ B
| A_BS_dioid  _ B                                        => A_bs_classify_dioid _ B
| A_BS_prelattice  _ B                                   => A_bs_classify_prelattice _ B
| A_BS_distributive_prelattice  _ B                      => A_bs_classify_distributive_prelattice _ B
| A_BS_lattice   _ B                                     => A_bs_classify_lattice _ B
| A_BS_distributive_lattice   _ B                        => A_bs_classify_distributive_lattice _ B
| A_BS_selective_presemiring   _ B                       => A_bs_classify_selective_presemiring _ B
| A_BS_selective_semiring  _ B                           => A_bs_classify_selective_semiring _ B
| A_BS_selective_pre_dioid _ B                           => A_bs_classify_selective_pre_dioid _ B
| A_BS_selective_pre_dioid_with_zero  _ B                => A_bs_classify_selective_pre_dioid_with_zero _ B
| A_BS_selective_pre_dioid_with_one   _ B                => A_bs_classify_selective_pre_dioid_with_one _ B
| A_BS_selective_dioid   _ B                             => A_bs_classify_selective_dioid _ B
| A_BS_selective_cancellative_pre_dioid  _ B             => A_bs_classify_selective_cancellative_pre_dioid _ B
| A_BS_selective_cancellative_pre_dioid_with_zero  _ B   => A_bs_classify_selective_cancellative_pre_dioid_with_zero _ B
| A_BS_selective_cancellative_pre_dioid_with_one   _ B   => A_bs_classify_selective_cancellative_pre_dioid_with_one _ B
| A_BS_selective_cancellative_dioid   _ B                => A_bs_classify_selective_cancellative_dioid _ B
| A_BS_selective_distributive_prelattice   _ B           => A_bs_classify_selective_distributive_prelattice _ B
| A_BS_selective_distributive_prelattice_with_zero   _ B => A_bs_classify_selective_distributive_prelattice_with_zero _ B
| A_BS_selective_distributive_prelattice_with_one   _ B  => A_bs_classify_selective_distributive_prelattice_with_one _ B
| A_BS_selective_distributive_lattice   _ B              => A_bs_classify_selective_distributive_lattice _ B
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
; bs_plus_certs    : sg_certificates (S := S) 
; bs_times_certs   : sg_certificates (S := S)
; bs_id_ann_certs  : id_ann_certificates (S := S)
; bs_certs         : bs_certificates (S := S)
; bs_ast           : cas_bs_ast
}.


Record bs_CS {S : Type} := {
  bs_CS_eqv          : eqv (S := S) 
; bs_CS_plus         : binary_op S 
; bs_CS_times        : binary_op S 
; bs_CS_plus_certs   : sg_CS_certificates (S := S) 
; bs_CS_times_certs  : sg_certificates (S := S)
; bs_CS_id_ann_certs : id_ann_certificates (S := S) 
; bs_CS_certs        : bs_certificates (S := S)
; bs_CS_ast          : cas_bs_ast
}.

Record bs_CI {S : Type} := {
  bs_CI_eqv          : eqv (S := S) 
; bs_CI_plus         : binary_op S 
; bs_CI_times        : binary_op S 
; bs_CI_plus_certs   : sg_CI_certificates (S := S) 
; bs_CI_times_certs  : sg_certificates (S := S)
; bs_CI_id_ann_certs : id_ann_certificates (S := S)               
; bs_CI_certs        : bs_certificates (S := S)
; bs_CI_ast          : cas_bs_ast
}.

Record presemiring {S : Type} := {
  presemiring_eqv          : @eqv S 
; presemiring_plus         : binary_op S 
; presemiring_times        : binary_op S 
; presemiring_plus_certs   : @sg_C_certificates S 
; presemiring_times_certs  : @sg_certificates S
; presemiring_id_ann_certs : @id_ann_certificates S
; presemiring_certs        : @semiring_certificates S
; presemiring_ast          : cas_bs_ast
}.

Record selective_presemiring {S : Type} := {
  selective_presemiring_eqv          : @eqv S 
; selective_presemiring_plus         : binary_op S 
; selective_presemiring_times        : binary_op S 
; selective_presemiring_plus_certs   : @sg_CS_certificates S 
; selective_presemiring_times_certs  : @sg_certificates S
; selective_presemiring_id_ann_certs : @id_ann_certificates S
; selective_presemiring_certs        : @semiring_certificates S
; selective_presemiring_ast          : cas_bs_ast
}.



Record semiring {S : Type} := {
  semiring_eqv          : @eqv S 
; semiring_plus         : binary_op S 
; semiring_times        : binary_op S 
; semiring_plus_certs   : @sg_C_certificates S 
; semiring_times_certs  : @sg_certificates S
; semiring_id_ann_certs : @pid_is_tann_certificates S
; semiring_certs        : @semiring_certificates S
; semiring_ast          : cas_bs_ast
}.

Record selective_semiring {S : Type} := {
  selective_semiring_eqv          : @eqv S 
; selective_semiring_plus         : binary_op S 
; selective_semiring_times        : binary_op S 
; selective_semiring_plus_certs   : @sg_CS_certificates S 
; selective_semiring_times_certs  : @sg_certificates S
; selective_semiring_id_ann_certs : @pid_is_tann_certificates S
; selective_semiring_certs        : @semiring_certificates S
; selective_semiring_ast          : cas_bs_ast
}.


Record pre_dioid {S : Type} := {
  pre_dioid_eqv          : @eqv S 
; pre_dioid_plus         : @binary_op S 
; pre_dioid_times        : @binary_op S 
; pre_dioid_plus_certs   : @sg_CI_certificates S 
; pre_dioid_times_certs  : @sg_certificates S 
; pre_dioid_id_ann_certs : @id_ann_certificates S 
; pre_dioid_certs        : @dioid_certificates S 
; pre_dioid_ast          : cas_bs_ast
}.

Record pre_dioid_with_one {S : Type} := {
  pre_dioid_with_one_eqv          : @eqv S 
; pre_dioid_with_one_plus         : @binary_op S 
; pre_dioid_with_one_times        : @binary_op S 
; pre_dioid_with_one_plus_certs   : @sg_CI_certificates S 
; pre_dioid_with_one_times_certs  : @sg_certificates S 
; pre_dioid_with_one_id_ann_certs : @pann_is_tid_certificates S 
; pre_dioid_with_one_certs        : @dioid_certificates S 
; pre_dioid_with_one_ast          : cas_bs_ast
}.

Record pre_dioid_with_zero {S : Type} := {
  pre_dioid_with_zero_eqv          : @eqv S 
; pre_dioid_with_zero_plus         : @binary_op S 
; pre_dioid_with_zero_times        : @binary_op S 
; pre_dioid_with_zero_plus_certs   : @sg_CI_certificates S 
; pre_dioid_with_zero_times_certs  : @sg_certificates S 
; pre_dioid_with_zero_id_ann_certs : @pid_is_tann_certificates S 
; pre_dioid_with_zero_certs        : @dioid_certificates S 
; pre_dioid_with_zero_ast          : cas_bs_ast
}.

Record dioid (S : Type) := {
  dioid_eqv           : @eqv S 
; dioid_plus          : binary_op S 
; dioid_times         : binary_op S 
; dioid_plus_certs    : @sg_CI_certificates S 
; dioid_times_certs   : @sg_certificates S 
; dioid_id_ann_certs  : @dually_bounded_certificates S 
; dioid_certs         : @dioid_certificates S 
; dioid_ast           : cas_bs_ast
}.


Record selective_pre_dioid (S : Type) := {
  selective_pre_dioid_eqv           : @eqv S 
; selective_pre_dioid_plus          : binary_op S 
; selective_pre_dioid_times         : binary_op S 
; selective_pre_dioid_plus_certs    : @sg_CS_certificates S 
; selective_pre_dioid_times_certs   : @sg_certificates S 
; selective_pre_dioid_id_ann_certs  : @id_ann_certificates S 
; selective_pre_dioid_certs         : @dioid_certificates S 
; selective_pre_dioid_ast           : cas_bs_ast
}.

Record selective_pre_dioid_with_one (S : Type) := {
  selective_pre_dioid_with_one_eqv           : @eqv S 
; selective_pre_dioid_with_one_plus          : binary_op S 
; selective_pre_dioid_with_one_times         : binary_op S 
; selective_pre_dioid_with_one_plus_certs    : @sg_CS_certificates S 
; selective_pre_dioid_with_one_times_certs   : @sg_certificates S 
; selective_pre_dioid_with_one_id_ann_certs  : @pann_is_tid_certificates S 
; selective_pre_dioid_with_one_certs         : @dioid_certificates S 
; selective_pre_dioid_with_one_ast           : cas_bs_ast
}.

Record selective_pre_dioid_with_zero (S : Type) := {
  selective_pre_dioid_with_zero_eqv           : @eqv S 
; selective_pre_dioid_with_zero_plus          : binary_op S 
; selective_pre_dioid_with_zero_times         : binary_op S 
; selective_pre_dioid_with_zero_plus_certs    : @sg_CS_certificates S 
; selective_pre_dioid_with_zero_times_certs   : @sg_certificates S 
; selective_pre_dioid_with_zero_id_ann_certs  : @pid_is_tann_certificates S 
; selective_pre_dioid_with_zero_certs         : @dioid_certificates S 
; selective_pre_dioid_with_zero_ast           : cas_bs_ast
}.


Record selective_dioid (S : Type) := {
  selective_dioid_eqv           : @eqv S 
; selective_dioid_plus          : binary_op S 
; selective_dioid_times         : binary_op S 
; selective_dioid_plus_certs    : @sg_CS_certificates S 
; selective_dioid_times_certs   : @sg_certificates S 
; selective_dioid_id_ann_certs  : @dually_bounded_certificates S 
; selective_dioid_certs         : @dioid_certificates S 
; selective_dioid_ast           : cas_bs_ast
}.


Record selective_cancellative_pre_dioid (S : Type) := {
  selective_cancellative_pre_dioid_eqv           : @eqv S 
; selective_cancellative_pre_dioid_plus          : binary_op S 
; selective_cancellative_pre_dioid_times         : binary_op S 
; selective_cancellative_pre_dioid_plus_certs    : @sg_CS_certificates S 
; selective_cancellative_pre_dioid_times_certs   : @sg_CK_certificates S 
; selective_cancellative_pre_dioid_id_ann_certs  : @id_ann_certificates S 
; selective_cancellative_pre_dioid_certs         : @dioid_certificates S 
; selective_cancellative_pre_dioid_ast           : cas_bs_ast
}.

Record selective_cancellative_pre_dioid_with_one (S : Type) := {
  selective_cancellative_pre_dioid_with_one_eqv           : @eqv S 
; selective_cancellative_pre_dioid_with_one_plus          : binary_op S 
; selective_cancellative_pre_dioid_with_one_times         : binary_op S 
; selective_cancellative_pre_dioid_with_one_plus_certs    : @sg_CS_certificates S 
; selective_cancellative_pre_dioid_with_one_times_certs   : @sg_CK_certificates S 
; selective_cancellative_pre_dioid_with_one_id_ann_certs  : @pann_is_tid_certificates S 
; selective_cancellative_pre_dioid_with_one_certs         : @dioid_certificates S 
; selective_cancellative_pre_dioid_with_one_ast           : cas_bs_ast
}.

Record selective_cancellative_pre_dioid_with_zero (S : Type) := {
  selective_cancellative_pre_dioid_with_zero_eqv           : @eqv S 
; selective_cancellative_pre_dioid_with_zero_plus          : binary_op S 
; selective_cancellative_pre_dioid_with_zero_times         : binary_op S 
; selective_cancellative_pre_dioid_with_zero_plus_certs    : @sg_CS_certificates S 
; selective_cancellative_pre_dioid_with_zero_times_certs   : @sg_CK_certificates S 
; selective_cancellative_pre_dioid_with_zero_id_ann_certs  : @pid_is_tann_certificates S 
; selective_cancellative_pre_dioid_with_zero_certs         : @dioid_certificates S 
; selective_cancellative_pre_dioid_with_zero_ast           : cas_bs_ast
}.


Record selective_cancellative_dioid (S : Type) := {
  selective_cancellative_dioid_eqv           : @eqv S 
; selective_cancellative_dioid_plus          : binary_op S 
; selective_cancellative_dioid_times         : binary_op S 
; selective_cancellative_dioid_plus_certs    : @sg_CS_certificates S 
; selective_cancellative_dioid_times_certs   : @sg_CK_certificates S 
; selective_cancellative_dioid_id_ann_certs  : @dually_bounded_certificates S 
; selective_cancellative_dioid_certs         : @dioid_certificates S 
; selective_cancellative_dioid_ast           : cas_bs_ast
}.



Record prelattice {S : Type} := {
  prelattice_eqv           : @eqv S 
; prelattice_join          : binary_op S 
; prelattice_meet          : binary_op S 
; prelattice_join_certs   : @sg_CI_certificates S 
; prelattice_meet_certs   : @sg_CI_certificates S 
; prelattice_id_ann_certs : @id_ann_certificates S 
; prelattice_certs        : @lattice_certificates S 
; prelattice_ast           : cas_bs_ast
}.

Record distributive_prelattice {S : Type} := {
  distributive_prelattice_eqv           : @eqv S 
; distributive_prelattice_join          : binary_op S 
; distributive_prelattice_meet          : binary_op S 
; distributive_prelattice_join_certs    : @sg_CI_certificates S 
; distributive_prelattice_meet_certs    : @sg_CI_certificates S 
; distributive_prelattice_id_ann_certs  : @id_ann_certificates S
; distributive_prelattice_certs         : @distributive_lattice_certificates S
; distributive_prelattice_ast           : cas_bs_ast
}.

Record selective_distributive_prelattice {S : Type} := {
  selective_distributive_prelattice_eqv          : @eqv S 
; selective_distributive_prelattice_join         : binary_op S 
; selective_distributive_prelattice_meet         : binary_op S 
; selective_distributive_prelattice_join_certs   : @sg_CS_certificates S
; selective_distributive_prelattice_meet_certs   : @sg_CS_certificates S 
; selective_distributive_prelattice_id_ann_certs : @id_ann_certificates S
; selective_distributive_prelattice_certs        : @distributive_lattice_certificates S
; selective_distributive_prelattice_ast          : cas_bs_ast
}.

Record selective_distributive_prelattice_with_zero {S : Type} := {
  selective_distributive_prelattice_with_zero_eqv          : @eqv S 
; selective_distributive_prelattice_with_zero_join         : binary_op S 
; selective_distributive_prelattice_with_zero_meet         : binary_op S 
; selective_distributive_prelattice_with_zero_join_certs   : @sg_CS_certificates S
; selective_distributive_prelattice_with_zero_meet_certs   : @sg_CS_certificates S 
; selective_distributive_prelattice_with_zero_id_ann_certs : @pid_is_tann_certificates S
; selective_distributive_prelattice_with_zero_certs        : @distributive_lattice_certificates S
; selective_distributive_prelattice_with_zero_ast          : cas_bs_ast
}.

Record selective_distributive_prelattice_with_one {S : Type} := {
  selective_distributive_prelattice_with_one_eqv          : @eqv S 
; selective_distributive_prelattice_with_one_join         : binary_op S 
; selective_distributive_prelattice_with_one_meet         : binary_op S 
; selective_distributive_prelattice_with_one_join_certs   : @sg_CS_certificates S
; selective_distributive_prelattice_with_one_meet_certs   : @sg_CS_certificates S 
; selective_distributive_prelattice_with_one_id_ann_certs : @pann_is_tid_certificates S
; selective_distributive_prelattice_with_one_certs        : @distributive_lattice_certificates S
; selective_distributive_prelattice_with_one_ast          : cas_bs_ast
}.

Record selective_distributive_lattice {S : Type} := {
  selective_distributive_lattice_eqv        : @eqv S 
; selective_distributive_lattice_join       : binary_op S 
; selective_distributive_lattice_meet       : binary_op S 
; selective_distributive_lattice_join_certs : @sg_CS_certificates S 
; selective_distributive_lattice_meet_certs : @sg_CS_certificates S
; selective_distributive_lattice_id_ann_certs : @dually_bounded_certificates S                                                                  
; selective_distributive_lattice_certs      : @distributive_lattice_certificates S
; selective_distributive_lattice_ast        : cas_bs_ast
}.


Record lattice {S : Type} := {
  lattice_eqv          : @eqv S 
; lattice_join         : binary_op S 
; lattice_meet         : binary_op S 
; lattice_join_certs   : @sg_CI_certificates S 
; lattice_meet_certs   : @sg_CI_certificates S
; lattice_id_ann_certs : @dually_bounded_certificates S
; lattice_certs        : @lattice_certificates S
; lattice_ast          : cas_bs_ast
}.


Record distributive_lattice {S : Type} := {
  distributive_lattice_eqv          : @eqv S 
; distributive_lattice_join         : binary_op S 
; distributive_lattice_meet         : binary_op S 
; distributive_lattice_join_certs   : @sg_CI_certificates S 
; distributive_lattice_meet_certs   : @sg_CI_certificates S
; distributive_lattice_id_ann_certs : @dually_bounded_certificates S
; distributive_lattice_certs        : @distributive_lattice_certificates S
; distributive_lattice_ast          : cas_bs_ast
}.
  
End CAS. 

Section MCAS.

Inductive bs_mcas {S : Type} :=
| BS_Error : list string            -> @bs_mcas S
| BS_bs : @bs S                    -> @bs_mcas S
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



Definition bs_classify_selective_distributive_lattice (S : Type) (B : @selective_distributive_lattice S) : @bs_mcas S :=
  BS_selective_distributive_lattice B. 

Definition bs_classify_selective_distributive_prelattice_with_one (S : Type) (B : @selective_distributive_prelattice_with_one S) : @bs_mcas S :=
  BS_selective_distributive_prelattice_with_one B. 

Definition bs_classify_selective_distributive_prelattice_with_zero (S : Type) (B : @selective_distributive_prelattice_with_zero S) : @bs_mcas S :=
  BS_selective_distributive_prelattice_with_zero B. 

Definition bs_classify_selective_distributive_prelattice (S : Type) (B : @selective_distributive_prelattice S) : @bs_mcas S :=
  BS_selective_distributive_prelattice B. 

Definition bs_classify_distributive_lattice (S : Type) (B : @distributive_lattice S) : @bs_mcas S :=
  BS_distributive_lattice B. 

Definition bs_classify_lattice  (S : Type) (B : @lattice  S) : @bs_mcas S :=
  BS_lattice  B. 

Definition bs_classify_distributive_prelattice (S : Type) (B : @distributive_prelattice S) : @bs_mcas S :=
  BS_distributive_prelattice B. 

Definition bs_classify_prelattice (S : Type) (B : @prelattice S) : @bs_mcas S :=
  BS_prelattice B. 

Definition bs_classify_selective_cancellative_dioid (S : Type) (B : @selective_cancellative_dioid S) : @bs_mcas S :=
  BS_selective_cancellative_dioid B. 

Definition bs_classify_selective_cancellative_pre_dioid_with_one (S : Type) (B : @selective_cancellative_pre_dioid_with_one S) : @bs_mcas S :=
  BS_selective_cancellative_pre_dioid_with_one B. 

Definition bs_classify_selective_cancellative_pre_dioid_with_zero (S : Type) (B : @selective_cancellative_pre_dioid_with_zero S) : @bs_mcas S :=
  BS_selective_cancellative_pre_dioid_with_zero B. 

Definition bs_classify_selective_cancellative_pre_dioid (S : Type) (B : @selective_cancellative_pre_dioid S) : @bs_mcas S :=
  BS_selective_cancellative_pre_dioid B. 

Definition bs_classify_selective_dioid (S : Type) (B : @selective_dioid S) : @bs_mcas S :=
  BS_selective_dioid B. 

Definition bs_classify_selective_pre_dioid_with_one (S : Type) (B : @selective_pre_dioid_with_one S) : @bs_mcas S :=
  BS_selective_pre_dioid_with_one B. 

Definition bs_classify_selective_pre_dioid_with_zero (S : Type) (B : @selective_pre_dioid_with_zero S) : @bs_mcas S :=
  BS_selective_pre_dioid_with_zero B. 

(*
  selective_pre_dioid 
  => selective_dioid 
  => selective_pre_dioid_with_one
  => selective_pre_dioid_with_zero 
 *)
Definition bs_classify_selective_pre_dioid (S : Type) (B : @selective_pre_dioid S) : @bs_mcas S :=

let eqv     := selective_pre_dioid_eqv _ B in
let plus    := selective_pre_dioid_plus _ B in
let times   := selective_pre_dioid_times _ B in    
let plusP   := selective_pre_dioid_plus_certs _ B in
let timesP  := selective_pre_dioid_times_certs _ B in
let id_annP := selective_pre_dioid_id_ann_certs _ B in
let bsP     := selective_pre_dioid_certs _ B in
let ast     := selective_pre_dioid_ast _ B in
match id_ann_plus_times_d id_annP,
      id_ann_times_plus_d id_annP
with
|  Id_Ann_Cert_Equal s1, Id_Ann_Cert_Equal s2 => BS_selective_dioid
   {|                                                               
      selective_dioid_eqv           := eqv 
    ; selective_dioid_plus          := plus
    ; selective_dioid_times         := times
    ; selective_dioid_plus_certs   := plusP 
    ; selective_dioid_times_certs  := timesP 
    ; selective_dioid_id_ann_certs :=
        {|
           bounded_plus_id_is_times_ann := Assert_Exists_Id_Ann_Equal s1
         ; bounded_times_id_is_plus_ann := Assert_Exists_Id_Ann_Equal s2
        |}
    ; selective_dioid_certs        := bsP 
    ; selective_dioid_ast           := ast 
   |}   
|  Id_Ann_Cert_Equal s, P2 => BS_selective_pre_dioid_with_zero
   {|                                                               
      selective_pre_dioid_with_zero_eqv           := eqv 
    ; selective_pre_dioid_with_zero_plus          := plus
    ; selective_pre_dioid_with_zero_times         := times
    ; selective_pre_dioid_with_zero_plus_certs   := plusP 
    ; selective_pre_dioid_with_zero_times_certs  := timesP 
    ; selective_pre_dioid_with_zero_id_ann_certs :=
        {|
           pid_is_tann_plus_times   := Assert_Exists_Id_Ann_Equal s
         ; pid_is_tann_times_plus_d := P2
        |}
    ; selective_pre_dioid_with_zero_certs        := bsP 
    ; selective_pre_dioid_with_zero_ast           := ast 
   |}   
|  P1, Id_Ann_Cert_Equal s => BS_selective_pre_dioid_with_one
   {|                                                               
      selective_pre_dioid_with_one_eqv           := eqv 
    ; selective_pre_dioid_with_one_plus          := plus
    ; selective_pre_dioid_with_one_times         := times
    ; selective_pre_dioid_with_one_plus_certs   := plusP 
    ; selective_pre_dioid_with_one_times_certs  := timesP 
    ; selective_pre_dioid_with_one_id_ann_certs :=
        {|
           pann_is_tid_plus_times_d := P1
         ; pann_is_tid_times_plus   := Assert_Exists_Id_Ann_Equal s
        |}
    ; selective_pre_dioid_with_one_certs        := bsP 
    ; selective_pre_dioid_with_one_ast           := ast 
   |}   
| _, _ => BS_selective_pre_dioid B
end. 

(* do we want a cancellative dioid? *) 
Definition bs_classify_dioid (S : Type) (B : @dioid S) : @bs_mcas S :=
  BS_dioid B. 

(*
  pre_dioid_with_zero
  => dioid
*) 
Definition bs_classify_pre_dioid_with_zero (S : Type) (B : @pre_dioid_with_zero S) : @bs_mcas S :=
let id_annP := pre_dioid_with_zero_id_ann_certs B in
match pid_is_tann_times_plus_d id_annP with
|  Id_Ann_Cert_Equal s => bs_classify_dioid _ 
   {|                                                               
      dioid_eqv           := pre_dioid_with_zero_eqv B
    ; dioid_plus          := pre_dioid_with_zero_plus B
    ; dioid_times         := pre_dioid_with_zero_times B 
    ; dioid_plus_certs   := pre_dioid_with_zero_plus_certs B 
    ; dioid_times_certs  := pre_dioid_with_zero_times_certs B 
    ; dioid_id_ann_certs :=
        {|
           bounded_plus_id_is_times_ann := pid_is_tann_plus_times  id_annP
         ; bounded_times_id_is_plus_ann := Assert_Exists_Id_Ann_Equal s
        |}
    ; dioid_certs        := pre_dioid_with_zero_certs B 
    ; dioid_ast           := pre_dioid_with_zero_ast B 
   |}   
| _ => BS_pre_dioid_with_zero B
end. 

(*
  pre_dioid_with_one 
  => dioid
*) 
Definition bs_classify_pre_dioid_with_one (S : Type) (B : @pre_dioid_with_one S) : @bs_mcas S :=
let id_annP := pre_dioid_with_one_id_ann_certs B in
match pann_is_tid_plus_times_d id_annP with
|  Id_Ann_Cert_Equal s => bs_classify_dioid _ 
   {|                                                               
      dioid_eqv           := pre_dioid_with_one_eqv B
    ; dioid_plus          := pre_dioid_with_one_plus B
    ; dioid_times         := pre_dioid_with_one_times B 
    ; dioid_plus_certs   := pre_dioid_with_one_plus_certs B 
    ; dioid_times_certs  := pre_dioid_with_one_times_certs B 
    ; dioid_id_ann_certs :=
        {|
           bounded_plus_id_is_times_ann := Assert_Exists_Id_Ann_Equal s
         ; bounded_times_id_is_plus_ann := pann_is_tid_times_plus id_annP
        |}
    ; dioid_certs        := pre_dioid_with_one_certs B 
    ; dioid_ast           := pre_dioid_with_one_ast B 
   |}   
| _ => BS_pre_dioid_with_one B
end. 

(* 
   pre_dioid
   => dioid
   => pre_dioid_with_zero
   => pre_dioid_with_one

*) 
Definition bs_classify_pre_dioid (S : Type) (B : @pre_dioid S) : @bs_mcas S :=
let eqv     := pre_dioid_eqv B in
let plus    := pre_dioid_plus B in
let times   := pre_dioid_times B in    
let plusP   := pre_dioid_plus_certs B in
let timesP  := pre_dioid_times_certs B in
let id_annP := pre_dioid_id_ann_certs B in
let bsP     := pre_dioid_certs B in
let ast     := pre_dioid_ast B in
match id_ann_plus_times_d id_annP,
      id_ann_times_plus_d id_annP
with
|  Id_Ann_Cert_Equal s1, Id_Ann_Cert_Equal s2 => BS_dioid 
   {|                                                               
      dioid_eqv           := eqv 
    ; dioid_plus          := plus
    ; dioid_times         := times
    ; dioid_plus_certs   := plusP 
    ; dioid_times_certs  := timesP 
    ; dioid_id_ann_certs :=
        {|
           bounded_plus_id_is_times_ann := Assert_Exists_Id_Ann_Equal s1
         ; bounded_times_id_is_plus_ann := Assert_Exists_Id_Ann_Equal s2
        |}
    ; dioid_certs        := bsP 
    ; dioid_ast           := ast 
   |}   
|  Id_Ann_Cert_Equal s, P2 => BS_pre_dioid_with_zero 
   {|                                                               
      pre_dioid_with_zero_eqv           := eqv 
    ; pre_dioid_with_zero_plus          := plus
    ; pre_dioid_with_zero_times         := times
    ; pre_dioid_with_zero_plus_certs   := plusP 
    ; pre_dioid_with_zero_times_certs  := timesP 
    ; pre_dioid_with_zero_id_ann_certs :=
        {|
           pid_is_tann_plus_times   := Assert_Exists_Id_Ann_Equal s
         ; pid_is_tann_times_plus_d := P2
        |}
    ; pre_dioid_with_zero_certs        := bsP 
    ; pre_dioid_with_zero_ast           := ast 
   |}   
|  P1, Id_Ann_Cert_Equal s => BS_pre_dioid_with_one 
   {|                                                               
      pre_dioid_with_one_eqv           := eqv 
    ; pre_dioid_with_one_plus          := plus
    ; pre_dioid_with_one_times         := times
    ; pre_dioid_with_one_plus_certs   := plusP 
    ; pre_dioid_with_one_times_certs  := timesP 
    ; pre_dioid_with_one_id_ann_certs :=
        {|
           pann_is_tid_plus_times_d   := P1
         ; pann_is_tid_times_plus := Assert_Exists_Id_Ann_Equal s
        |}
    ; pre_dioid_with_one_certs        := bsP 
    ; pre_dioid_with_one_ast           := ast 
   |}   
| _, _ => BS_pre_dioid B
end. 
  

(*
    selective_semiring
     => selective_pre_dioid_with_zero
 *)
Definition bs_classify_selective_semiring (S : Type) (B : @selective_semiring S) : @bs_mcas S :=
let P := selective_semiring_certs B in
match semiring_left_left_absorptive_d P,
      semiring_left_right_absorptive_d P
with
|  Certify_Left_Left_Absorptive, Certify_Left_Right_Absorptive =>
   bs_classify_selective_pre_dioid_with_zero _ 
   {|                                                               
      selective_pre_dioid_with_zero_eqv           := selective_semiring_eqv B
    ; selective_pre_dioid_with_zero_plus          := selective_semiring_plus B
    ; selective_pre_dioid_with_zero_times         := selective_semiring_times B 
    ; selective_pre_dioid_with_zero_plus_certs   := selective_semiring_plus_certs B 
    ; selective_pre_dioid_with_zero_times_certs  := selective_semiring_times_certs B 
    ; selective_pre_dioid_with_zero_id_ann_certs := selective_semiring_id_ann_certs B
    ; selective_pre_dioid_with_zero_certs        :=
                {|
                    dioid_left_distributive     := semiring_left_distributive P
                  ; dioid_right_distributive    := semiring_right_distributive P
                  ; dioid_left_left_absorptive  := Assert_Left_Left_Absorptive
                  ; dioid_left_right_absorptive := Assert_Left_Right_Absorptive
                 |} 
    ; selective_pre_dioid_with_zero_ast           := selective_semiring_ast B 
   |}   
| _, _ => BS_selective_semiring B
end. 


(*
   selective_presemiring
   => selective_semiring
   => selective_pre_dioid
*) 
Definition bs_classify_selective_presemiring (S : Type) (B : @selective_presemiring S) : @bs_mcas S :=
let eqv     := selective_presemiring_eqv B in
let plus    := selective_presemiring_plus B in
let times   := selective_presemiring_times B in    
let plusP   := selective_presemiring_plus_certs B in
let timesP  := selective_presemiring_times_certs B in
let id_annP := selective_presemiring_id_ann_certs B in
let bsP     := selective_presemiring_certs B in
let ast     := selective_presemiring_ast B in
match semiring_left_left_absorptive_d bsP,
      semiring_left_right_absorptive_d bsP
with
|  Certify_Left_Left_Absorptive, Certify_Left_Right_Absorptive =>  
  bs_classify_selective_pre_dioid _
       {|                                                         
           selective_pre_dioid_eqv           := eqv
         ; selective_pre_dioid_plus          := plus
         ; selective_pre_dioid_times         := times
         ; selective_pre_dioid_plus_certs   := plusP
         ; selective_pre_dioid_times_certs  := timesP
         ; selective_pre_dioid_id_ann_certs := id_annP
         ; selective_pre_dioid_certs        :=
                {|
                    dioid_left_distributive     := semiring_left_distributive bsP
                  ; dioid_right_distributive    := semiring_right_distributive bsP
                  ; dioid_left_left_absorptive  := Assert_Left_Left_Absorptive
                  ; dioid_left_right_absorptive := Assert_Left_Right_Absorptive
                 |} 
         ; selective_pre_dioid_ast           := ast 
       |}         
| _, _ =>
  match id_ann_plus_times_d id_annP with
  | Id_Ann_Cert_Equal s => bs_classify_selective_semiring _
          {| 
              selective_semiring_eqv           := eqv
            ; selective_semiring_plus          := plus
            ; selective_semiring_times         := times
            ; selective_semiring_plus_certs   := plusP
            ; selective_semiring_times_certs  := timesP
            ; selective_semiring_id_ann_certs :=
               {|
                   pid_is_tann_plus_times   := Assert_Exists_Id_Ann_Equal s
                 ; pid_is_tann_times_plus_d := id_ann_times_plus_d  id_annP 
              |}
            ; selective_semiring_certs        := bsP 
            ; selective_semiring_ast           := ast 
           |}                               
  | _ => BS_selective_presemiring B
  end
end. 


(* 
   semiring
   => selective_semiring 
   => pre_dioid_with_zero 
 *)
Definition bs_classify_semiring (S : Type) (B : @semiring S) : @bs_mcas S :=
let plusP   := semiring_plus_certs B in
let srP     := semiring_certs B in  
match sg_C_selective_d plusP with  
| Certify_Selective => bs_classify_selective_semiring _
          {|
              selective_semiring_eqv           := semiring_eqv B 
            ; selective_semiring_plus          := semiring_plus B 
            ; selective_semiring_times         := semiring_times B 
            ; selective_semiring_plus_certs   :=
                {|
                    sg_CS_associative := sg_C_associative plusP
                  ; sg_CS_congruence  := sg_C_congruence plusP
                  ; sg_CS_commutative := sg_C_commutative plusP
                  ; sg_CS_selective   := Assert_Selective 
                |}
            ; selective_semiring_times_certs  := semiring_times_certs B
            ; selective_semiring_id_ann_certs := semiring_id_ann_certs B 
            ; selective_semiring_certs        := semiring_certs B 
            ; selective_semiring_ast           := semiring_ast B 
          |}                          
| Certify_Not_Selective (s1, s2) =>
  match sg_C_idempotent_d plusP,
        semiring_left_left_absorptive_d srP,
        semiring_left_right_absorptive_d srP
  with
  |  Certify_Idempotent, Certify_Left_Left_Absorptive, Certify_Left_Right_Absorptive =>      
     bs_classify_pre_dioid_with_zero _
          {|
              pre_dioid_with_zero_eqv           := semiring_eqv B 
            ; pre_dioid_with_zero_plus          := semiring_plus B 
            ; pre_dioid_with_zero_times         := semiring_times B 
            ; pre_dioid_with_zero_plus_certs   :=
                {|
                    sg_CI_associative   := sg_C_associative plusP
                  ; sg_CI_congruence    := sg_C_congruence plusP
                  ; sg_CI_commutative   := sg_C_commutative plusP
                  ; sg_CI_idempotent    := Assert_Idempotent
                  ; sg_CI_not_selective := Assert_Not_Selective (s1, s2)
                |}
            ; pre_dioid_with_zero_times_certs  := semiring_times_certs B
            ; pre_dioid_with_zero_id_ann_certs := semiring_id_ann_certs B
            ; pre_dioid_with_zero_certs        :=
                {|
                    dioid_left_distributive     := semiring_left_distributive srP
                  ; dioid_right_distributive    := semiring_right_distributive srP
                  ; dioid_left_left_absorptive  := Assert_Left_Left_Absorptive
                  ; dioid_left_right_absorptive := Assert_Left_Right_Absorptive
                 |}
            ; pre_dioid_with_zero_ast           := semiring_ast B 
          |}      
  | _, _, _ => BS_semiring B    
  end 
end. 

(* 
   presemiring
   => selective_presemiring 
   => semiring 
 *)
Definition bs_classify_presemiring (S : Type) (B : @presemiring S) : @bs_mcas S :=
let plusP   := presemiring_plus_certs B in
let srP     := presemiring_certs B in    
match sg_C_selective_d plusP with
| Certify_Selective => bs_classify_selective_presemiring _
          {|
              selective_presemiring_eqv           := presemiring_eqv B 
            ; selective_presemiring_plus          := presemiring_plus B 
            ; selective_presemiring_times         := presemiring_times B 
            ; selective_presemiring_plus_certs   :=
                {|
                    sg_CS_associative := sg_C_associative plusP
                  ; sg_CS_congruence  := sg_C_congruence plusP
                  ; sg_CS_commutative := sg_C_commutative plusP
                  ; sg_CS_selective   := Assert_Selective 
                |}
            ; selective_presemiring_times_certs  := presemiring_times_certs B
            ; selective_presemiring_id_ann_certs := presemiring_id_ann_certs B 
            ; selective_presemiring_certs        := presemiring_certs B 
            ; selective_presemiring_ast           := presemiring_ast B 
          |}
| Certify_Not_Selective (s1, s2) =>
  match id_ann_plus_times_d (presemiring_id_ann_certs B) with
  | Id_Ann_Cert_Equal s => bs_classify_semiring _
          {|
              semiring_eqv           := presemiring_eqv B 
            ; semiring_plus          := presemiring_plus B 
            ; semiring_times         := presemiring_times B 
            ; semiring_plus_certs   := presemiring_plus_certs B 
            ; semiring_times_certs  := presemiring_times_certs B
            ; semiring_id_ann_certs :=
                {|
                   pid_is_tann_plus_times   := Assert_Exists_Id_Ann_Equal s
                 ; pid_is_tann_times_plus_d := id_ann_times_plus_d (presemiring_id_ann_certs B)
                |}                
            ; semiring_certs        := presemiring_certs B 
            ; semiring_ast          := presemiring_ast B 
          |}      
  | _ => 
    match sg_C_idempotent_d plusP,
        semiring_left_left_absorptive_d srP,
        semiring_left_right_absorptive_d srP
    with
    |  Certify_Idempotent, Certify_Left_Left_Absorptive, Certify_Left_Right_Absorptive =>      
       bs_classify_pre_dioid _
          {|
              pre_dioid_eqv           := presemiring_eqv B 
            ; pre_dioid_plus          := presemiring_plus B 
            ; pre_dioid_times         := presemiring_times B 
            ; pre_dioid_plus_certs   :=
                {|
                    sg_CI_associative   := sg_C_associative plusP
                  ; sg_CI_congruence    := sg_C_congruence plusP
                  ; sg_CI_commutative   := sg_C_commutative plusP
                  ; sg_CI_idempotent    := Assert_Idempotent
                  ; sg_CI_not_selective := Assert_Not_Selective (s1, s2)
                |}
            ; pre_dioid_times_certs  := presemiring_times_certs B
            ; pre_dioid_id_ann_certs := presemiring_id_ann_certs B
            ; pre_dioid_certs        :=
                {|
                    dioid_left_distributive     := semiring_left_distributive srP
                  ; dioid_right_distributive    := semiring_right_distributive srP
                  ; dioid_left_left_absorptive  := Assert_Left_Left_Absorptive
                  ; dioid_left_right_absorptive := Assert_Left_Right_Absorptive
                 |}
            ; pre_dioid_ast           := presemiring_ast B 
          |}      
  | _, _, _ => BS_presemiring B          
    end 
  end 
end. 
  

(*
 bs_CS
 => selective_presemiring 
*) 
Definition bs_classify_bs_CS (S : Type) (B : @bs_CS S) : @bs_mcas S :=
let eqv     := bs_CS_eqv B in
let plus    := bs_CS_plus B in
let times   := bs_CS_times B in    
let plusP   := bs_CS_plus_certs B in
let timesP  := bs_CS_times_certs B in
let id_annP := bs_CS_id_ann_certs B in
let bsP     := bs_CS_certs B in
let ast     := bs_CS_ast B in
match bs_left_distributive_d bsP,
      bs_right_distributive_d bsP
with
| Certify_Left_Distributive,  Certify_Right_Distributive =>
  bs_classify_selective_presemiring _
          {|
              selective_presemiring_eqv           := eqv
            ; selective_presemiring_plus           := plus
            ; selective_presemiring_times         := times
            ; selective_presemiring_plus_certs   := plusP
            ; selective_presemiring_times_certs  := timesP
            ; selective_presemiring_id_ann_certs := id_annP 
            ; selective_presemiring_certs        :=
                {|
                    semiring_left_distributive       := Assert_Left_Distributive
                  ; semiring_right_distributive      := Assert_Right_Distributive
                  ; semiring_left_left_absorptive_d  := bs_left_left_absorptive_d bsP
                  ; semiring_left_right_absorptive_d := bs_left_right_absorptive_d bsP
                 |} 
            ; selective_presemiring_ast           := ast 
          |}                          
| _, _ => BS_bs_CS B 
end. 

(*
   classify 
   bs_CI
   --> pre_dioid
   --> pre_lattice (* not yet, need dual properties in bs! *) 
*) 
Definition bs_classify_bs_CI (S : Type) (B : @bs_CI S) : @bs_mcas S :=
let eqv     := bs_CI_eqv B in
let plus    := bs_CI_plus B in
let times   := bs_CI_times B in    
let plusP   := bs_CI_plus_certs B in
let timesP  := bs_CI_times_certs B in
let id_annP := bs_CI_id_ann_certs B in
let bsP     := bs_CI_certs B in
let ast     := bs_CI_ast B in
match bs_left_distributive_d bsP,
      bs_right_distributive_d bsP,
      bs_left_left_absorptive_d bsP,       
      bs_left_right_absorptive_d bsP
with
| Certify_Left_Distributive,
  Certify_Right_Distributive,
  Certify_Left_Left_Absorptive,
  Certify_Left_Right_Absorptive
  =>  bs_classify_pre_dioid _
          {|
              pre_dioid_eqv           := eqv
            ; pre_dioid_plus          := plus
            ; pre_dioid_times         := times
            ; pre_dioid_plus_certs   := plusP
            ; pre_dioid_times_certs  := timesP
            ; pre_dioid_id_ann_certs := id_annP 
            ; pre_dioid_certs        :=
                {|
                    dioid_left_distributive     := Assert_Left_Distributive
                  ; dioid_right_distributive    := Assert_Right_Distributive
                  ; dioid_left_left_absorptive  := Assert_Left_Left_Absorptive
                  ; dioid_left_right_absorptive := Assert_Left_Right_Absorptive
                 |} 
            ; pre_dioid_ast           := ast 
          |}                          
| _, _, _, _ => BS_bs_CI B 
end. 


(*
   classify 
   bs 
   --> bs_CI
   --> bs_CI
   --> bs_presemiring
   --> bs_selective_presemiring
*) 

Definition bs_classify_bs (S : Type) (B : @bs S) : @bs_mcas S :=
let eqv     := bs_eqv B in
let plus    := bs_plus B in
let times   := bs_times B in    
let plusP   := bs_plus_certs B in
let timesP  := bs_times_certs B in
let id_annP := bs_id_ann_certs B in
let bsP     := bs_certs B in
let ast     := bs_ast B in
match sg_commutative_d plusP with
| Certify_Commutative =>
  match sg_idempotent_d plusP with
  | Certify_Idempotent =>
    match sg_selective_d plusP with
    | Certify_Selective =>
      let sg_CS_P :=
                  {|
                      sg_CS_associative := sg_associative plusP 
                    ; sg_CS_congruence  := sg_congruence plusP 
                    ; sg_CS_commutative := Assert_Commutative
                    ; sg_CS_selective   := Assert_Selective
                  |} in           
      match bs_left_distributive_d bsP with
      | Certify_Left_Distributive =>
        match bs_right_distributive_d bsP with
        | Certify_Right_Distributive => bs_classify_selective_presemiring _ 
                 {|
                     selective_presemiring_eqv           := eqv
                   ; selective_presemiring_plus          := plus
                   ; selective_presemiring_times         := times 
                   ; selective_presemiring_plus_certs   := sg_CS_P
                   ; selective_presemiring_times_certs  := timesP 
                   ; selective_presemiring_id_ann_certs := id_annP
                   ; selective_presemiring_certs        :=
                       {|
                           semiring_left_distributive       := Assert_Left_Distributive
                         ; semiring_right_distributive      := Assert_Right_Distributive
                         ; semiring_left_left_absorptive_d  := bs_left_left_absorptive_d bsP
                         ; semiring_left_right_absorptive_d := bs_left_right_absorptive_d bsP
                       |}
                   ; selective_presemiring_ast           := ast
                  |}
        | _ => bs_classify_bs_CS _
                  {|
                      bs_CS_eqv           := eqv
                    ; bs_CS_plus          := plus 
                    ; bs_CS_times         := times 
                    ; bs_CS_plus_certs   := sg_CS_P  
                    ; bs_CS_times_certs  := timesP
                    ; bs_CS_id_ann_certs := id_annP
                    ; bs_CS_certs        := bsP 
                    ; bs_CS_ast           := ast 
                  |}                                         
        end 
      | _ => bs_classify_bs_CS _
                  {|
                      bs_CS_eqv           := eqv
                    ; bs_CS_plus          := plus 
                    ; bs_CS_times         := times 
                    ; bs_CS_plus_certs   := sg_CS_P  
                    ; bs_CS_times_certs  := timesP
                    ; bs_CS_id_ann_certs := id_annP
                    ; bs_CS_certs        := bsP 
                    ; bs_CS_ast           := ast 
                  |} 
      end 
    | Certify_Not_Selective (s1, s2) =>
      let sg_CI_P :=
                  {|
                      sg_CI_associative   := sg_associative plusP 
                    ; sg_CI_congruence    := sg_congruence plusP 
                    ; sg_CI_commutative   := Assert_Commutative
                    ; sg_CI_idempotent    := Assert_Idempotent
                    ; sg_CI_not_selective := Assert_Not_Selective (s1, s2)
                  |} in           
      match bs_left_distributive_d bsP with
      | Certify_Left_Distributive =>
        match bs_right_distributive_d bsP with
        | Certify_Right_Distributive => bs_classify_presemiring _
                 {|
                     presemiring_eqv           := eqv
                   ; presemiring_plus          := plus
                   ; presemiring_times         := times 
                   ; presemiring_plus_certs   :=
                        {|
                            sg_C_associative  := sg_associative plusP 
                          ; sg_C_congruence   := sg_congruence plusP 
                          ; sg_C_commutative  := Assert_Commutative
                          ; sg_C_selective_d  := sg_selective_d plusP
                          ; sg_C_idempotent_d := sg_idempotent_d plusP
                          ; sg_C_anti_left_d  := sg_anti_left_d plusP
                          ; sg_C_anti_right_d := sg_anti_right_d plusP
                          ; sg_C_cancel_d     := sg_left_cancel_d plusP
                          ; sg_C_constant_d   := sg_left_constant_d plusP                                                   
                        |} 
                   ; presemiring_times_certs  := timesP 
                   ; presemiring_id_ann_certs := id_annP
                   ; presemiring_certs        :=
                       {|
                           semiring_left_distributive       := Assert_Left_Distributive
                         ; semiring_right_distributive      := Assert_Right_Distributive
                         ; semiring_left_left_absorptive_d  := bs_left_left_absorptive_d bsP
                         ; semiring_left_right_absorptive_d := bs_left_right_absorptive_d bsP
                       |}
                   ; presemiring_ast           := ast
                  |}
        | _ => bs_classify_bs_CI _
                  {|
                      bs_CI_eqv           := eqv
                    ; bs_CI_plus          := plus 
                    ; bs_CI_times         := times 
                    ; bs_CI_plus_certs   := sg_CI_P  
                    ; bs_CI_times_certs  := timesP
                    ; bs_CI_id_ann_certs := id_annP
                    ; bs_CI_certs        := bsP 
                    ; bs_CI_ast           := ast 
                  |}                                         
        end 
      | _ => bs_classify_bs_CI _
                  {|
                      bs_CI_eqv           := eqv
                    ; bs_CI_plus          := plus 
                    ; bs_CI_times         := times 
                    ; bs_CI_plus_certs   := sg_CI_P  
                    ; bs_CI_times_certs  := timesP
                    ; bs_CI_id_ann_certs := id_annP
                    ; bs_CI_certs        := bsP 
                    ; bs_CI_ast           := ast 
                  |} 
      end 
    end
  | nidem => (* not idempotent *) 
    match bs_left_distributive_d bsP with
    | Certify_Left_Distributive =>
      match bs_right_distributive_d bsP with
      | Certify_Right_Distributive => bs_classify_presemiring _
                  {|
                      presemiring_eqv          := eqv  
                    ; presemiring_plus         := plus
                    ; presemiring_times        := times 
                    ; presemiring_plus_certs  :=
                        {|
                            sg_C_associative  := sg_associative plusP 
                          ; sg_C_congruence   := sg_congruence plusP 
                          ; sg_C_commutative  := Assert_Commutative
                          ; sg_C_selective_d  := sg_selective_d plusP
                          ; sg_C_idempotent_d := nidem
                          ; sg_C_anti_left_d  := sg_anti_left_d plusP
                          ; sg_C_anti_right_d := sg_anti_right_d plusP
                          ; sg_C_cancel_d     := sg_left_cancel_d plusP
                          ; sg_C_constant_d   := sg_left_constant_d plusP                                                   
                        |} 
                    ; presemiring_times_certs := timesP
                    ; presemiring_id_ann_certs := id_annP                                                      
                    ; presemiring_certs       :=
                        {|                        
                           semiring_left_distributive       := Assert_Left_Distributive
                         ; semiring_right_distributive      := Assert_Right_Distributive
                         ; semiring_left_left_absorptive_d  := bs_left_left_absorptive_d bsP
                         ; semiring_left_right_absorptive_d := bs_left_right_absorptive_d bsP
                        |}                         
                    ; presemiring_ast          := ast 
                  |}
      | _ => BS_bs B                       
      end 
    | _ => BS_bs B               
    end 
  end 
| _ => BS_bs B               
end.

Definition bs_classify {S : Type} (A : @bs_mcas S) : @bs_mcas S := 
match A with
| BS_Error _                                         => A
| BS_bs B                                            => bs_classify_bs _ B
| BS_bs_CI B                                         => bs_classify_bs_CI _ B
| BS_bs_CS B                                         => bs_classify_bs_CS _ B
| BS_presemiring B                                   => bs_classify_presemiring _ B
| BS_semiring B                                      => bs_classify_semiring _ B
| BS_pre_dioid B                                     => bs_classify_pre_dioid _ B
| BS_pre_dioid_with_one B                            => bs_classify_pre_dioid_with_one _ B
| BS_pre_dioid_with_zero B                           => bs_classify_pre_dioid_with_zero _ B
| BS_dioid  B                                        => bs_classify_dioid _ B
| BS_prelattice  B                                   => bs_classify_prelattice _ B
| BS_distributive_prelattice  B                      => bs_classify_distributive_prelattice _ B
| BS_lattice   B                                     => bs_classify_lattice _ B
| BS_distributive_lattice   B                        => bs_classify_distributive_lattice _ B
| BS_selective_presemiring   B                       => bs_classify_selective_presemiring _ B
| BS_selective_semiring  B                           => bs_classify_selective_semiring _ B
| BS_selective_pre_dioid B                           => bs_classify_selective_pre_dioid _ B
| BS_selective_pre_dioid_with_zero  B                => bs_classify_selective_pre_dioid_with_zero _ B
| BS_selective_pre_dioid_with_one   B                => bs_classify_selective_pre_dioid_with_one _ B
| BS_selective_dioid   B                             => bs_classify_selective_dioid _ B
| BS_selective_cancellative_pre_dioid  B             => bs_classify_selective_cancellative_pre_dioid _ B
| BS_selective_cancellative_pre_dioid_with_zero  B   => bs_classify_selective_cancellative_pre_dioid_with_zero _ B
| BS_selective_cancellative_pre_dioid_with_one   B   => bs_classify_selective_cancellative_pre_dioid_with_one _ B
| BS_selective_cancellative_dioid   B                => bs_classify_selective_cancellative_dioid _ B
| BS_selective_distributive_prelattice   B           => bs_classify_selective_distributive_prelattice _ B
| BS_selective_distributive_prelattice_with_zero   B => bs_classify_selective_distributive_prelattice_with_zero _ B
| BS_selective_distributive_prelattice_with_one   B  => bs_classify_selective_distributive_prelattice_with_one _ B
| BS_selective_distributive_lattice   B              => bs_classify_selective_distributive_lattice _ B
end. 



End MCAS.   


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
; bs_plus_certs  := P2C_sg S (A_eqv_eq S (A_bs_eqv S R)) 
                                (A_bs_plus S R) 
                                (A_bs_plus_proofs S R)
; bs_times_certs := P2C_sg S (A_eqv_eq S (A_bs_eqv S R)) 
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
; bs_CS_times_certs := P2C_sg S (A_eqv_eq S (A_bs_CS_eqv S R)) 
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
; bs_CI_times_certs := P2C_sg S (A_eqv_eq S (A_bs_CI_eqv S R)) 
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
; presemiring_times_certs := P2C_sg S (A_eqv_eq S (A_presemiring_eqv S R)) 
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
; selective_presemiring_times_certs := P2C_sg S (A_eqv_eq S (A_selective_presemiring_eqv S R)) 
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
; semiring_times_certs := P2C_sg S (A_eqv_eq S (A_semiring_eqv S R)) 
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
; selective_semiring_times_certs := P2C_sg S (A_eqv_eq S (A_selective_semiring_eqv S R)) 
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


Definition A2C_prelattice : ∀ (S : Type), A_prelattice S -> @prelattice S 
:= λ S R,
{|
  prelattice_eqv         := A2C_eqv S (A_prelattice_eqv S R)
; prelattice_join        := A_prelattice_join S R 
; prelattice_meet        := A_prelattice_meet S R 
; prelattice_join_certs  := P2C_sg_CI S (A_eqv_eq S (A_prelattice_eqv S R)) 
                                (A_prelattice_join S R) 
                                (A_prelattice_join_proofs S R)
; prelattice_meet_certs := P2C_sg_CI S (A_eqv_eq S (A_prelattice_eqv S R)) 
                                (A_prelattice_meet S R) 
                                (A_prelattice_meet_proofs S R)
; prelattice_id_ann_certs := P2C_id_ann S (A_eqv_eq S (A_prelattice_eqv S R)) 
                                   (A_prelattice_join S R) 
                                   (A_prelattice_meet S R) 
                                   (A_prelattice_id_ann_proofs S R)         
; prelattice_certs       := P2C_lattice S 
                                        (A_eqv_eq S (A_prelattice_eqv S R)) 
                                        (A_prelattice_join S R)
                                        (A_prelattice_meet S R)                   
                                        (A_prelattice_proofs S R)
; prelattice_ast        := A_prelattice_ast S R
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
; pre_dioid_times_certs  := P2C_sg S _ _  (A_pre_dioid_times_proofs S P) 
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
; pre_dioid_with_one_times_certs  := P2C_sg S _ _  (A_pre_dioid_with_one_times_proofs S P) 
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
; pre_dioid_with_zero_times_certs  := P2C_sg S _ _  (A_pre_dioid_with_zero_times_proofs S P) 
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
; dioid_times_certs  := P2C_sg S _ _  (A_dioid_times_proofs S P) 
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
; selective_pre_dioid_times_certs   := P2C_sg S _ _  (A_selective_pre_dioid_times_proofs S P) 
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
; selective_pre_dioid_with_one_times_certs   := P2C_sg S _ _  (A_selective_pre_dioid_with_one_times_proofs S P) 
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
; selective_pre_dioid_with_zero_times_certs   := P2C_sg S _ _  (A_selective_pre_dioid_with_zero_times_proofs S P)  
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
; selective_dioid_times_certs  := P2C_sg S _ _  (A_selective_dioid_times_proofs S P) 
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

Definition A2C_mcas_bs (S : Type) (A : A_bs_mcas S) : @bs_mcas S := 
match A with   
| A_BS_Error _ l => BS_Error l
| A_BS_bs _ B    => BS_bs (A2C_bs _ B)
| A_BS_bs_CI _ B => BS_bs_CI (A2C_bs_CI _ B)
| A_BS_bs_CS _ B => BS_bs_CS (A2C_bs_CS _ B)
| A_BS_presemiring _ B => BS_presemiring (A2C_presemiring _ B)
| A_BS_semiring _ B => BS_semiring (A2C_semiring _ B)
| A_BS_pre_dioid _ B => BS_pre_dioid (A2C_pre_dioid _ B)
| A_BS_pre_dioid_with_one _ B => BS_pre_dioid_with_one (A2C_pre_dioid_with_one _ B)
| A_BS_pre_dioid_with_zero _ B => BS_pre_dioid_with_zero (A2C_pre_dioid_with_zero _ B)
| A_BS_dioid _ B => BS_dioid (A2C_dioid _ B)
| A_BS_prelattice _ B => BS_prelattice (A2C_prelattice _ B)
| A_BS_distributive_prelattice _ B => BS_distributive_prelattice (A2C_distributive_prelattice _ B)
| A_BS_lattice _ B => BS_lattice (A2C_lattice _ B)
| A_BS_distributive_lattice _ B => BS_distributive_lattice (A2C_distributive_lattice _ B)
| A_BS_selective_presemiring  _ B => BS_selective_presemiring (A2C_selective_presemiring _ B)
| A_BS_selective_semiring _ B => BS_selective_semiring (A2C_selective_semiring _ B)
| A_BS_selective_pre_dioid _ B => BS_selective_pre_dioid (A2C_selective_pre_dioid _ B)
| A_BS_selective_pre_dioid_with_zero _ B => BS_selective_pre_dioid_with_zero (A2C_selective_pre_dioid_with_zero _ B)
| A_BS_selective_pre_dioid_with_one _ B => BS_selective_pre_dioid_with_one (A2C_selective_pre_dioid_with_one _ B)
| A_BS_selective_dioid _ B => BS_selective_dioid (A2C_selective_dioid _ B)
| A_BS_selective_cancellative_pre_dioid _ B => BS_selective_cancellative_pre_dioid (A2C_selective_cancellative_pre_dioid _ B)
| A_BS_selective_cancellative_pre_dioid_with_zero _ B => BS_selective_cancellative_pre_dioid_with_zero (A2C_selective_cancellative_pre_dioid_with_zero _ B)
| A_BS_selective_cancellative_pre_dioid_with_one _ B => BS_selective_cancellative_pre_dioid_with_one (A2C_selective_cancellative_pre_dioid_with_one _ B)
| A_BS_selective_cancellative_dioid  _ B => BS_selective_cancellative_dioid (A2C_selective_cancellative_dioid _ B)
| A_BS_selective_distributive_prelattice _ B => BS_selective_distributive_prelattice (A2C_selective_distributive_prelattice _ B)
| A_BS_selective_distributive_prelattice_with_zero _ B => BS_selective_distributive_prelattice_with_zero (A2C_selective_distributive_prelattice_with_zero _ B)
| A_BS_selective_distributive_prelattice_with_one _ B => BS_selective_distributive_prelattice_with_one (A2C_selective_distributive_prelattice_with_one _ B)
| A_BS_selective_distributive_lattice _ B => BS_selective_distributive_lattice (A2C_selective_distributive_lattice _ B)
end.

End Translation. 

Section Verify.

Variable S : Type.

 
Lemma correct_bs_classify_selective_distributive_lattice (a : A_selective_distributive_lattice S) :
  bs_classify_selective_distributive_lattice S (A2C_selective_distributive_lattice S a)
  =
  A2C_mcas_bs S (A_bs_classify_selective_distributive_lattice S a). 
Proof. unfold bs_classify_selective_distributive_lattice, 
              A_bs_classify_selective_distributive_lattice.
       reflexivity.
Qed. 

Lemma correct_bs_classify_selective_distributive_prelattice_with_one (a : A_selective_distributive_prelattice_with_one S) :
  bs_classify_selective_distributive_prelattice_with_one S (A2C_selective_distributive_prelattice_with_one S a)
  =
  A2C_mcas_bs S (A_bs_classify_selective_distributive_prelattice_with_one S a). 
Proof. unfold bs_classify_selective_distributive_prelattice_with_one,
             A_bs_classify_selective_distributive_prelattice_with_one. 
       reflexivity.
Qed. 

Lemma correct_bs_classify_selective_distributive_prelattice_with_zero (a : A_selective_distributive_prelattice_with_zero S) :
  bs_classify_selective_distributive_prelattice_with_zero S (A2C_selective_distributive_prelattice_with_zero S a)
  =
  A2C_mcas_bs S (A_bs_classify_selective_distributive_prelattice_with_zero S a). 
Proof. unfold bs_classify_selective_distributive_prelattice_with_zero,
            A_bs_classify_selective_distributive_prelattice_with_zero.
       reflexivity.
Qed.            

Lemma correct_bs_classify_selective_distributive_prelattice (a : A_selective_distributive_prelattice S) :
  bs_classify_selective_distributive_prelattice S (A2C_selective_distributive_prelattice S a)
  =
  A2C_mcas_bs S (A_bs_classify_selective_distributive_prelattice S a). 
Proof. unfold bs_classify_selective_distributive_prelattice,
       A_bs_classify_selective_distributive_prelattice. 
       reflexivity.
Qed.                                    


Lemma correct_bs_classify_distributive_lattice (a : A_distributive_lattice S) :
  bs_classify_distributive_lattice S (A2C_distributive_lattice S a)
  =
  A2C_mcas_bs S (A_bs_classify_distributive_lattice S a). 
Proof. unfold bs_classify_distributive_lattice,
       A_bs_classify_distributive_lattice.
       reflexivity.
Qed.                                    

Lemma correct_bs_classify_lattice (a : A_lattice S) :
  bs_classify_lattice S (A2C_lattice S a)
  =
 A2C_mcas_bs S (A_bs_classify_lattice S a). 
Proof. unfold bs_classify_lattice, A_bs_classify_lattice.
       reflexivity.
Qed.                                   

Lemma correct_bs_classify_distributive_prelattice (a : A_distributive_prelattice S) :
  bs_classify_distributive_prelattice S (A2C_distributive_prelattice S a)
  =
 A2C_mcas_bs S (A_bs_classify_distributive_prelattice S a). 
Proof. unfold bs_classify_distributive_prelattice,
       A_bs_classify_distributive_prelattice.
       reflexivity.
Qed.   

Lemma correct_bs_classify_prelattice (a : A_prelattice S) :
  bs_classify_prelattice S (A2C_prelattice S a)
  =
 A2C_mcas_bs S (A_bs_classify_prelattice S a). 
Proof. unfold bs_classify_prelattice, A_bs_classify_prelattice.
       reflexivity.
Qed.            

Lemma correct_bs_classify_selective_cancellative_dioid (a : A_selective_cancellative_dioid S) :
  bs_classify_selective_cancellative_dioid S (A2C_selective_cancellative_dioid S a)
  =
 A2C_mcas_bs S (A_bs_classify_selective_cancellative_dioid S a). 
Proof. unfold bs_classify_selective_cancellative_dioid,
       A_bs_classify_selective_cancellative_dioid.
       reflexivity.
Qed.            

Lemma correct_bs_classify_selective_cancellative_pre_dioid_with_one (a : A_selective_cancellative_pre_dioid_with_one S) :
  bs_classify_selective_cancellative_pre_dioid_with_one S (A2C_selective_cancellative_pre_dioid_with_one S a)
  =
 A2C_mcas_bs S (A_bs_classify_selective_cancellative_pre_dioid_with_one S a). 
Proof. unfold bs_classify_selective_cancellative_pre_dioid_with_one,
       A_bs_classify_selective_cancellative_pre_dioid_with_one.
       reflexivity.
Qed.            

Lemma correct_bs_classify_selective_cancellative_pre_dioid_with_zero (a : A_selective_cancellative_pre_dioid_with_zero S) :
  bs_classify_selective_cancellative_pre_dioid_with_zero S (A2C_selective_cancellative_pre_dioid_with_zero S a)
  =
 A2C_mcas_bs S (A_bs_classify_selective_cancellative_pre_dioid_with_zero S a). 
Proof. unfold bs_classify_selective_cancellative_pre_dioid_with_zero,
       A_bs_classify_selective_cancellative_pre_dioid_with_zero. 
       reflexivity.
Qed.            

Lemma correct_bs_classify_selective_cancellative_pre_dioid (a : A_selective_cancellative_pre_dioid S) :
  bs_classify_selective_cancellative_pre_dioid S (A2C_selective_cancellative_pre_dioid S a)
  =
 A2C_mcas_bs S (A_bs_classify_selective_cancellative_pre_dioid S a). 
Proof. unfold bs_classify_selective_cancellative_pre_dioid,
       A_bs_classify_selective_cancellative_pre_dioid.
       reflexivity.
Qed.            

Lemma correct_bs_classify_selective_dioid (a : A_selective_dioid S) :
  bs_classify_selective_dioid S (A2C_selective_dioid S a)
  =
 A2C_mcas_bs S (A_bs_classify_selective_dioid S a). 
Proof. unfold bs_classify_selective_dioid,
       A_bs_classify_selective_dioid.
       reflexivity.
Qed.            


Lemma correct_bs_classify_selective_pre_dioid_with_one (a : A_selective_pre_dioid_with_one S) :
  bs_classify_selective_pre_dioid_with_one S (A2C_selective_pre_dioid_with_one S a)
  =
 A2C_mcas_bs S (A_bs_classify_selective_pre_dioid_with_one S a). 
Proof. unfold bs_classify_selective_pre_dioid_with_one,
       A_bs_classify_selective_pre_dioid_with_one.
       reflexivity.
Qed.        

Lemma correct_bs_classify_selective_pre_dioid_with_zero (a : A_selective_pre_dioid_with_zero S) :
 bs_classify_selective_pre_dioid_with_zero S (A2C_selective_pre_dioid_with_zero S a)
 =
 A2C_mcas_bs S (A_bs_classify_selective_pre_dioid_with_zero S a). 
Proof. unfold bs_classify_selective_pre_dioid_with_zero,
       A_bs_classify_selective_pre_dioid_with_zero.
       reflexivity.
Qed.        


Lemma correct_bs_classify_dioid (a : A_dioid S) :
  bs_classify_dioid S (A2C_dioid S a)
  =
  A2C_mcas_bs S (A_bs_classify_dioid S a).   
Proof. unfold bs_classify_dioid, A_bs_classify_dioid.
       reflexivity.
Qed.            



(*
  selective_pre_dioid 
  => selective_dioid 
  => selective_pre_dioid_with_one
  => selective_pre_dioid_with_zero 

Note on the proof style used here.  Spelling out each step explicitly (rather than 
using tactics) makes it easir to evolve the classification code .... 
 *)
Lemma correct_bs_classify_selective_pre_dioid (a : A_selective_pre_dioid S) :
  bs_classify_selective_pre_dioid S (A2C_selective_pre_dioid S a)
  =
  A2C_mcas_bs S (A_bs_classify_selective_pre_dioid S a).   
Proof. destruct a, A_selective_pre_dioid_id_ann_proofs0. 
       unfold bs_classify_selective_pre_dioid, A_bs_classify_selective_pre_dioid; simpl.
       destruct A_id_ann_plus_times_d0. 
       + destruct p as [A B]; unfold p2c_exists_id_ann.
         destruct A_id_ann_times_plus_d0.
         ++ destruct p as [C D]; unfold p2c_exists_id_ann.
            unfold A2C_mcas_bs. reflexivity. 
         ++ destruct p as [C D]; unfold p2c_exists_id_ann.
            unfold A2C_mcas_bs. reflexivity.
         ++ destruct p as [C D]; unfold p2c_exists_id_ann.
            unfold A2C_mcas_bs. reflexivity.
         ++ unfold A2C_mcas_bs. reflexivity.
         ++ unfold A2C_mcas_bs. reflexivity.
       + destruct p as [A B]; unfold p2c_exists_id_ann.
         destruct A_id_ann_times_plus_d0.
         ++ destruct p as [C D]; unfold p2c_exists_id_ann.
            unfold A2C_mcas_bs. reflexivity.
         ++ destruct p as [C D]; unfold p2c_exists_id_ann.
            unfold A2C_mcas_bs. reflexivity.
         ++ destruct p as [C D]; unfold p2c_exists_id_ann.
            unfold A2C_mcas_bs. reflexivity.
         ++ unfold A2C_mcas_bs. reflexivity.
         ++ unfold A2C_mcas_bs. reflexivity.
       + destruct p as [A B]; unfold p2c_exists_id_ann.
         destruct A_id_ann_times_plus_d0.
         ++ destruct p as [C D]; unfold p2c_exists_id_ann.
            unfold A2C_mcas_bs. reflexivity.
         ++ destruct p as [C D]; unfold p2c_exists_id_ann.
            unfold A2C_mcas_bs. reflexivity.
         ++ destruct p as [C D]; unfold p2c_exists_id_ann.
            unfold A2C_mcas_bs. reflexivity.
         ++ unfold A2C_mcas_bs. reflexivity.
         ++ unfold A2C_mcas_bs. reflexivity.
       + unfold p2c_exists_id_ann.
         destruct A_id_ann_times_plus_d0.
         ++ destruct p as [C D]; unfold p2c_exists_id_ann.
            unfold A2C_mcas_bs. reflexivity.
         ++ destruct p as [C D]; unfold p2c_exists_id_ann.
            unfold A2C_mcas_bs. reflexivity.
         ++ destruct p as [C D]; unfold p2c_exists_id_ann.
            unfold A2C_mcas_bs. reflexivity.
         ++ unfold A2C_mcas_bs. reflexivity.
         ++ unfold A2C_mcas_bs. reflexivity.
       + unfold p2c_exists_id_ann.
         destruct A_id_ann_times_plus_d0.
         ++ destruct p as [C D]; unfold p2c_exists_id_ann.
            unfold A2C_mcas_bs. reflexivity.
         ++ destruct p as [C D]; unfold p2c_exists_id_ann.
            unfold A2C_mcas_bs. reflexivity.
         ++ destruct p as [C D]; unfold p2c_exists_id_ann.
            unfold A2C_mcas_bs. reflexivity.
         ++ unfold A2C_mcas_bs. reflexivity.
         ++ unfold A2C_mcas_bs. reflexivity.
Qed. 

(*
  pre_dioid_with_zero
  => dioid
*) 
Lemma correct_bs_classify_pre_dioid_with_zero (a : A_pre_dioid_with_zero S) :
  bs_classify_pre_dioid_with_zero S (A2C_pre_dioid_with_zero S a)
  =
  A2C_mcas_bs S (A_bs_classify_pre_dioid_with_zero S a).   
Proof. destruct a.
       unfold bs_classify_pre_dioid_with_zero,
       A_bs_classify_pre_dioid_with_zero; simpl.
       case_eq(A_pre_dioid_with_zero_id_ann_proofs0).
       intros H1 H2 H3. unfold p2c_exists_id_ann; simpl. 
       case_eq H2; intros [H4 H5] H6. 
       + unfold A2C_mcas_bs. reflexivity.
       + unfold A2C_mcas_bs. reflexivity.
       + unfold A2C_mcas_bs. reflexivity.
       + rewrite <- correct_bs_classify_dioid. reflexivity.
       + unfold A2C_mcas_bs. reflexivity.                        
Qed. 


Lemma correct_bs_classify_pre_dioid_with_one (a : A_pre_dioid_with_one S) :
  bs_classify_pre_dioid_with_one S (A2C_pre_dioid_with_one S a)
  =
  A2C_mcas_bs S (A_bs_classify_pre_dioid_with_one S a). 
Proof. destruct a.
       unfold bs_classify_pre_dioid_with_one,
       A_bs_classify_pre_dioid_with_one; simpl.
       case_eq(A_pre_dioid_with_one_id_ann_proofs0).
       intros H1 H2 H3. unfold p2c_exists_id_ann; simpl. 
       case_eq H1; intros [H4 H5] H6.
       + unfold A2C_mcas_bs. reflexivity.
       + unfold A2C_mcas_bs. reflexivity.
       + unfold A2C_mcas_bs. reflexivity.
       + unfold A2C_mcas_bs. reflexivity.
       + unfold A2C_mcas_bs. reflexivity.                        
Qed. 


Lemma correct_bs_classify_pre_dioid (a : A_pre_dioid S) :
  bs_classify_pre_dioid S (A2C_pre_dioid S a)
  =
 A2C_mcas_bs S (A_bs_classify_pre_dioid S a).   
Proof. destruct a, A_pre_dioid_id_ann_proofs0.
       unfold bs_classify_pre_dioid, A_bs_classify_pre_dioid; simpl.
       destruct A_id_ann_plus_times_d0.
       + destruct p as [A B]; unfold p2c_exists_id_ann; 
           destruct A_id_ann_times_plus_d0.
         ++ destruct p as [C D]. reflexivity. 
         ++ destruct p as [C D]. reflexivity. 
         ++ destruct p as [C D]. reflexivity. 
         ++ unfold A2C_mcas_bs. reflexivity.               
         ++ unfold A2C_mcas_bs. reflexivity.               
       + destruct p as [C D]. unfold p2c_exists_id_ann;
          destruct A_id_ann_times_plus_d0.
         ++ destruct p as [E F]. reflexivity. 
         ++ destruct p as [E F]. reflexivity. 
         ++ destruct p as [E F]. reflexivity. 
         ++ unfold A2C_mcas_bs. reflexivity.               
         ++ unfold A2C_mcas_bs. reflexivity.               
       + destruct p as [A B]; unfold p2c_exists_id_ann; 
           destruct A_id_ann_times_plus_d0.
         ++ destruct p as [C D]. reflexivity. 
         ++ destruct p as [C D]. reflexivity. 
         ++ destruct p as [C D]. reflexivity. 
         ++ unfold A2C_mcas_bs. reflexivity.               
         ++ unfold A2C_mcas_bs. reflexivity.               
       + unfold p2c_exists_id_ann; destruct A_id_ann_times_plus_d0.
         ++ destruct p as [C D]. reflexivity. 
         ++ destruct p as [C D]. reflexivity. 
         ++ destruct p as [C D]. reflexivity. 
         ++ unfold A2C_mcas_bs. reflexivity.               
         ++ unfold A2C_mcas_bs. reflexivity.               
       + unfold p2c_exists_id_ann; destruct A_id_ann_times_plus_d0.
         ++ destruct p as [C D]. reflexivity. 
         ++ destruct p as [C D]. reflexivity. 
         ++ destruct p as [C D]. reflexivity. 
         ++ unfold A2C_mcas_bs. reflexivity.               
         ++ unfold A2C_mcas_bs. reflexivity.               
Qed. 


Lemma correct_bs_classify_selective_semiring (a : A_selective_semiring S) :
  bs_classify_selective_semiring S (A2C_selective_semiring S a)
  =
  A2C_mcas_bs S (A_bs_classify_selective_semiring S a).   
Proof. destruct a, A_selective_semiring_proofs0. 
       unfold bs_classify_selective_semiring, A_bs_classify_selective_semiring; simpl. 
       destruct A_semiring_left_left_absorptive_d0 as [LLA | NLLA];
         unfold p2c_left_left_absorptive.
       + destruct A_semiring_left_right_absorptive_d0 as [LRA | NLRA];
           unfold p2c_left_right_absorptive.
         ++ rewrite <- correct_bs_classify_selective_pre_dioid_with_zero. reflexivity. 
         ++ unfold A2C_mcas_bs. reflexivity.                          
       + unfold A2C_mcas_bs. reflexivity.               
Qed. 


Lemma correct_bs_classify_selective_presemiring (a : A_selective_presemiring S) :
  bs_classify_selective_presemiring S (A2C_selective_presemiring S a)
  =
  A2C_mcas_bs S (A_bs_classify_selective_presemiring S a).   
Proof. destruct a. destruct A_selective_presemiring_proofs0. 
       unfold bs_classify_selective_presemiring,
       A_bs_classify_selective_presemiring; simpl.
       destruct A_semiring_left_left_absorptive_d0 as [LLA | NLLA];
         unfold p2c_left_left_absorptive.
       + destruct A_semiring_left_right_absorptive_d0 as [LRA | NLRA];
           unfold p2c_left_right_absorptive.
         ++ rewrite <- correct_bs_classify_selective_pre_dioid. reflexivity. 
         ++ destruct A_selective_presemiring_id_ann_proofs0.
            unfold p2c_exists_id_ann; simpl.
            destruct A_id_ann_plus_times_d0.
            +++ destruct p as [A B]. unfold A2C_mcas_bs. reflexivity.  
            +++ destruct p as [A B]. unfold A2C_mcas_bs. reflexivity.  
            +++ destruct p as [A B]. unfold A2C_mcas_bs. reflexivity.  
            +++ rewrite <- correct_bs_classify_selective_semiring. reflexivity. 
            +++ unfold A2C_mcas_bs. reflexivity.               
       + destruct A_selective_presemiring_id_ann_proofs0.
         unfold p2c_exists_id_ann; simpl.
         destruct A_id_ann_plus_times_d0.
         ++ destruct p as [A B]. unfold A2C_mcas_bs. reflexivity.  
         ++ destruct p as [A B]. unfold A2C_mcas_bs. reflexivity.  
         ++ destruct p as [A B]. unfold A2C_mcas_bs. reflexivity.  
         ++ rewrite <- correct_bs_classify_selective_semiring. reflexivity. 
         ++ unfold A2C_mcas_bs. reflexivity.               
Qed. 

Lemma correct_bs_classify_semiring (a : A_semiring S) :
  bs_classify_semiring S (A2C_semiring S a)
  =
 A2C_mcas_bs S (A_bs_classify_semiring S a).   
Proof. destruct a, A_semiring_plus_proofs0, A_semiring_proofs0.
       unfold bs_classify_semiring, A_bs_classify_semiring; simpl. 
       destruct A_sg_C_selective_d as [sel | [[s1 s2] nsel]];
         unfold p2c_selective_check; simpl. 
       +  rewrite <- correct_bs_classify_selective_semiring. reflexivity. 
       + destruct A_sg_C_idempotent_d as [idem | [s3 nidem]];
           unfold p2c_idempotent_check; simpl.
         ++ destruct A_semiring_left_left_absorptive_d0 as [LLA | NLLA];
              unfold p2c_left_left_absorptive.
            +++ destruct A_semiring_left_right_absorptive_d0 as [LRA | NLRA];
                  unfold p2c_left_right_absorptive.
                ++++ rewrite <- correct_bs_classify_pre_dioid_with_zero. reflexivity. 
                ++++ unfold A2C_mcas_bs. reflexivity.  
            +++ unfold A2C_mcas_bs. reflexivity.  
         ++ unfold A2C_mcas_bs. reflexivity.  
Qed.            

Lemma correct_bs_classify_presemiring (a : A_presemiring S) :
  bs_classify_presemiring S (A2C_presemiring S a)
  =
 A2C_mcas_bs S (A_bs_classify_presemiring S a).   
Proof. destruct a, A_presemiring_plus_proofs0, A_presemiring_proofs0. 
       unfold bs_classify_presemiring, A_bs_classify_presemiring. simpl. 
       destruct A_sg_C_selective_d as [sel | [[s1 s2] nsel]]; unfold p2c_selective_check.
       + rewrite <- correct_bs_classify_selective_presemiring. reflexivity. 
       + case_eq(A_presemiring_id_ann_proofs0); 
         intros H1 H2 H3; simpl;
         case_eq H1; 
         intros [H4 H5] H6; unfold p2c_exists_id_ann.
         ++ destruct A_sg_C_idempotent_d as [idem | [i nidem]]; unfold p2c_idempotent_check.
            +++ destruct A_semiring_left_left_absorptive_d0 as [LLA | NLLA];
                  unfold p2c_left_left_absorptive.
                ++++ destruct A_semiring_left_right_absorptive_d0 as [LRA | NLRA];
                       unfold p2c_left_right_absorptive.
                     +++++ rewrite <- correct_bs_classify_pre_dioid. reflexivity. 
                     +++++ unfold A2C_mcas_bs. reflexivity.                        
                ++++ unfold A2C_mcas_bs. reflexivity.  
            +++ unfold A2C_mcas_bs. reflexivity.  
         ++ destruct A_sg_C_idempotent_d as [idem | [i nidem]]; unfold p2c_idempotent_check.
            +++ destruct A_semiring_left_left_absorptive_d0 as [LLA | NLLA];
                  unfold p2c_left_left_absorptive.
                ++++ destruct A_semiring_left_right_absorptive_d0 as [LRA | NLRA];
                       unfold p2c_left_right_absorptive.
                     +++++ rewrite <- correct_bs_classify_pre_dioid. reflexivity. 
                     +++++ unfold A2C_mcas_bs. reflexivity.                        
                ++++ unfold A2C_mcas_bs. reflexivity.  
            +++ unfold A2C_mcas_bs. reflexivity.  
         ++ destruct A_sg_C_idempotent_d as [idem | [i nidem]]; unfold p2c_idempotent_check.
            +++ destruct A_semiring_left_left_absorptive_d0 as [LLA | NLLA];
                  unfold p2c_left_left_absorptive.
                ++++ destruct A_semiring_left_right_absorptive_d0 as [LRA | NLRA];
                       unfold p2c_left_right_absorptive.
                     +++++ rewrite <- correct_bs_classify_pre_dioid. reflexivity. 
                     +++++ unfold A2C_mcas_bs. reflexivity.                        
                ++++ unfold A2C_mcas_bs. reflexivity.  
            +++ unfold A2C_mcas_bs. reflexivity.  
         ++ destruct A_sg_C_idempotent_d as [idem | [i nidem]]; unfold p2c_idempotent_check.
            +++ destruct A_semiring_left_left_absorptive_d0 as [LLA | NLLA];
                  unfold p2c_left_left_absorptive.
                ++++ destruct A_semiring_left_right_absorptive_d0 as [LRA | NLRA];
                       unfold p2c_left_right_absorptive.
                     +++++ rewrite <- correct_bs_classify_semiring. reflexivity. (* NB *)
                     +++++ unfold A2C_mcas_bs. reflexivity.                        
                ++++ unfold A2C_mcas_bs. reflexivity.  
            +++ unfold A2C_mcas_bs. reflexivity.  
         ++ destruct A_sg_C_idempotent_d as [idem | [i nidem]]; unfold p2c_idempotent_check.
            +++ destruct A_semiring_left_left_absorptive_d0 as [LLA | NLLA];
                  unfold p2c_left_left_absorptive.
                ++++ destruct A_semiring_left_right_absorptive_d0 as [LRA | NLRA];
                       unfold p2c_left_right_absorptive.
                     +++++ rewrite <- correct_bs_classify_pre_dioid. reflexivity. 
                     +++++ unfold A2C_mcas_bs. reflexivity.                        
                ++++ unfold A2C_mcas_bs. reflexivity.  
            +++ unfold A2C_mcas_bs. reflexivity.  
Qed. 



Lemma correct_bs_classify_bs_CS (a : A_bs_CS S) : 
  bs_classify_bs_CS S (A2C_bs_CS S a)
  =
  A2C_mcas_bs S (A_bs_classify_bs_CS S a). 
Proof. destruct a, A_bs_CS_proofs0. 
       unfold bs_classify_bs_CS, A_bs_classify_bs_CS; simpl.
       destruct A_bs_left_distributive_d0 as [LD | NLD];
         unfold p2c_left_distributive.
       + destruct A_bs_right_distributive_d0 as [RD | NRD];
           unfold p2c_right_distributive.
         ++ rewrite <- correct_bs_classify_selective_presemiring. reflexivity. 
         ++ unfold A2C_mcas_bs. reflexivity.  
       + unfold A2C_mcas_bs. reflexivity.  
Qed.

Lemma correct_bs_classify_bs_CI (a : A_bs_CI S) : 
  bs_classify_bs_CI S (A2C_bs_CI S a)
  =
  A2C_mcas_bs S (A_bs_classify_bs_CI S a). 
Proof. destruct a, A_bs_CI_proofs0. 
       unfold bs_classify_bs_CI, A_bs_classify_bs_CI; simpl.
       destruct A_bs_left_distributive_d0 as [LD | NLD];
         unfold p2c_left_distributive.
       + destruct A_bs_right_distributive_d0 as [RD | NRD];
           unfold p2c_right_distributive.
         ++ destruct A_bs_left_left_absorptive_d0 as [LLA | NLLA];
              unfold p2c_left_left_absorptive.
            +++ destruct A_bs_left_right_absorptive_d0 as [LRA | NLRA];
                  unfold p2c_left_right_absorptive.
                ++++ rewrite <- correct_bs_classify_pre_dioid. reflexivity. 
                ++++ unfold A2C_mcas_bs. reflexivity.  
            +++ unfold A2C_mcas_bs. reflexivity.  
         ++ unfold A2C_mcas_bs. reflexivity.  
       + unfold A2C_mcas_bs. reflexivity.  
Qed.

Lemma correct_bs_classify_bs (A : A_bs S) :
  bs_classify_bs S (A2C_bs S A)
  =
  A2C_mcas_bs S (A_bs_classify_bs S A). 
Proof. destruct A, A_bs_plus_proofs0, A_bs_proofs0. 
       unfold bs_classify_bs, A_bs_classify_bs; simpl. 
       destruct A_sg_commutative_d as [commS | ncommS]; 
         unfold p2c_commutative_check.
       + destruct A_sg_idempotent_d as [idemS | nidemS]; 
           unfold p2c_idempotent_check.
         ++ destruct A_sg_selective_d as [selS | [[s1 s2] nselS]]; 
              unfold p2c_selective_check.
            +++ destruct A_bs_left_distributive_d0 as [LD | NLD];
                  unfold p2c_left_distributive.
                ++++ destruct A_bs_right_distributive_d0 as [RD | NRD];
                       unfold p2c_right_distributive.
                     +++++ rewrite <- correct_bs_classify_selective_presemiring. reflexivity. 
                     +++++ rewrite <- correct_bs_classify_bs_CS. reflexivity.                       
                ++++ rewrite <- correct_bs_classify_bs_CS. reflexivity.                       
            +++ unfold projT1.
                destruct A_bs_left_distributive_d0 as [LD | NLD];
                  unfold p2c_left_distributive.
                ++++ destruct A_bs_right_distributive_d0 as [RD | NRD];
                       unfold p2c_right_distributive.
                     +++++ rewrite <- correct_bs_classify_presemiring. reflexivity. 
                     +++++ rewrite <- correct_bs_classify_bs_CI. reflexivity.                       
                ++++ rewrite <- correct_bs_classify_bs_CI. reflexivity.  
         ++ destruct A_bs_left_distributive_d0 as [LD | NLD];
              unfold p2c_left_distributive.
            +++ destruct A_bs_right_distributive_d0 as [RD | NRD];
                       unfold p2c_right_distributive.
                ++++ rewrite <- correct_bs_classify_presemiring. reflexivity. 
                ++++ unfold A2C_mcas_bs. reflexivity.  
            +++ unfold A2C_mcas_bs. reflexivity.  
       + reflexivity. 
Qed. 
       
Theorem correct_bs_classify (A : A_bs_mcas S) :   
  bs_classify (A2C_mcas_bs S A)
  =
  A2C_mcas_bs S (A_bs_classify S A).
Proof. unfold bs_classify, A_bs_classify; destruct A; simpl.
       + reflexivity.
       + apply correct_bs_classify_bs.
       + apply correct_bs_classify_bs_CI.
       + apply correct_bs_classify_bs_CS.
       + apply correct_bs_classify_presemiring .
       + apply correct_bs_classify_semiring.
       + apply correct_bs_classify_pre_dioid.
       + apply correct_bs_classify_pre_dioid_with_one.
       + apply correct_bs_classify_pre_dioid_with_zero.
       + apply correct_bs_classify_dioid.
       + apply correct_bs_classify_prelattice.
       + apply correct_bs_classify_distributive_prelattice .
       + apply correct_bs_classify_lattice.
       + apply correct_bs_classify_distributive_lattice.
       + apply correct_bs_classify_selective_presemiring.
       + apply correct_bs_classify_selective_semiring .
       + apply correct_bs_classify_selective_pre_dioid .
       + apply correct_bs_classify_selective_pre_dioid_with_zero.
       + apply correct_bs_classify_selective_pre_dioid_with_one.
       + apply correct_bs_classify_selective_dioid. 
       + apply correct_bs_classify_selective_cancellative_pre_dioid .
       + apply correct_bs_classify_selective_cancellative_pre_dioid_with_zero .
       + apply correct_bs_classify_selective_cancellative_pre_dioid_with_one.
       + apply correct_bs_classify_selective_cancellative_dioid .
       + apply correct_bs_classify_selective_distributive_prelattice .
       + apply correct_bs_classify_selective_distributive_prelattice_with_zero.
       + apply correct_bs_classify_selective_distributive_prelattice_with_one .
       + apply correct_bs_classify_selective_distributive_lattice .
Qed. 

End Verify.   

