Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.os.properties.

Section ACAS.

Record os_bottom_top_proofs (S: Type) (eq lte : brel S) (times : binary_op S) := 
{
  A_bottom_top_bottom_id_d : os_exists_bottom_id_decidable S eq lte times 
; A_bottom_top_top_ann_d   : os_exists_top_ann_decidable S eq lte times 
}.

Record os_bottom_is_id_proofs (S: Type) (eq lte : brel S) (times : binary_op S) := 
{
  A_bottom_is_id           : os_exists_bottom_id_equal eq lte times 
; A_bottom_is_id_top_ann_d : os_exists_top_ann_decidable S eq lte times 
}.

Record os_top_is_ann_proofs (S: Type) (eq lte : brel S) (times : binary_op S) := 
{
  A_top_is_ann_bottom_id_d : os_exists_bottom_id_decidable S eq lte times 
; A_top_is_ann             : os_exists_top_ann_equal eq lte times 
}.


Record os_bounded_proofs (S: Type) (eq lte : brel S) (times : binary_op S) := 
{
  A_bounded_bottom_id : os_exists_bottom_id_equal eq lte times 
; A_bounded_top_ann   : os_exists_top_ann_equal eq lte times 
}.


Record os_proofs (S: Type) (lte : brel S) (times : binary_op S) := 
{
  A_posg_left_monotonic_d            : os_left_monotone_decidable lte times 
; A_posg_right_monotonic_d           : os_left_monotone_decidable lte times 

; A_posg_left_increasing_d           : os_left_increasing_decidable lte times 
; A_posg_right_increasing_d          : os_right_increasing_decidable lte times 

; A_posg_left_strictly_increasing_d  : os_left_strictly_increasing_decidable lte times 
; A_posg_right_strictly_increasing_d : os_right_strictly_increasing_decidable lte times 
}.


Record os_monotone_proofs (S: Type) (lte : brel S) (times : binary_op S) := 
{
  A_mono_left_monotonic              : os_left_monotone lte times 
; A_mono_right_monotonic             : os_right_monotone lte times 

; A_mono_left_increasing_d           : os_left_increasing_decidable lte times 
; A_mono_right_increasing_d          : os_right_increasing_decidable lte times 

; A_mono_left_strictly_increasing_d  : os_left_strictly_increasing_decidable lte times 
; A_mono_right_strictly_increasing_d : os_right_strictly_increasing_decidable lte times 
}. 


Record os_monotone_increasing_proofs (S: Type) (lte : brel S) (times : binary_op S) := 
{
  A_mono_inc_left_monotonic              : os_left_monotone lte times 
; A_mono_inc_right_monotonic             : os_right_monotone lte times 

; A_mono_inc_left_increasing             : os_left_increasing lte times 
; A_mono_inc_right_increasing            : os_right_increasing lte times 

; A_mono_inc_left_strictly_increasing_d  : os_left_strictly_increasing_decidable lte times 
; A_mono_inc_right_strictly_increasing_d : os_right_strictly_increasing_decidable lte times 
}. 


Record os_monotone_strictly_increasing_proofs (S: Type) (lte : brel S) (times : binary_op S) := 
{
  A_mono_sinc_left_monotonic              : os_left_monotone lte times 
; A_mono_sinc_right_monotonic             : os_right_monotone lte times 

; A_mono_sinc_left_strictly_increasing_d  : os_left_strictly_increasing_decidable lte times 
; A_mono_sinc_right_strictly_increasing_d : os_right_strictly_increasing_decidable lte times 
}. 


Record meet_semilattice_proofs {S : Type} (eq lte : brel S) (meet : binary_op S) := {
  A_msl_lte_proofs    : po_proofs S eq lte 
; A_msl_meet_proofs   : sg_CI_proofs S eq meet 
; A_msl_glb           : bop_is_glb lte meet 
}.

Record join_semilattice_proofs {S : Type} (eq lte : brel S) (join : binary_op S) := {
  A_jsl_lte_proofs    : po_proofs S eq lte 
; A_jsl_join_proofs   : sg_CI_proofs S eq join
; A_jsl_lub           : bop_is_lub lte join
}.


Record A_posg (S : Type) := {
  A_posg_eqv               : A_eqv S 
; A_posg_lte               : brel S 
; A_posg_times             : binary_op S 
; A_posg_lte_proofs        : po_proofs S (A_eqv_eq S A_posg_eqv) A_posg_lte
; A_posg_times_proofs      : msg_proofs S (A_eqv_eq S A_posg_eqv) A_posg_times
; A_posg_bottom_top_proofs : os_bottom_top_proofs S (A_eqv_eq S A_posg_eqv) A_posg_lte A_posg_times
; A_posg_proofs            : os_proofs S A_posg_lte A_posg_times 
; A_posg_ast               : cas_ast
}.

Record A_monotone_posg (S : Type) := {
  A_mposg_eqv          : A_eqv S 
; A_mposg_lte          : brel S 
; A_mposg_times        : binary_op S 
; A_mposg_lte_proofs   : po_proofs S (A_eqv_eq S A_mposg_eqv) A_mposg_lte
; A_mposg_times_proofs : msg_proofs S (A_eqv_eq S A_mposg_eqv) A_mposg_times
; A_mposg_top_bottom   : os_bottom_top_proofs S (A_eqv_eq S A_mposg_eqv) A_mposg_lte A_mposg_times                                    
; A_mposg_proofs       : os_monotone_proofs S A_mposg_lte A_mposg_times 
; A_mposg_ast          : cas_ast
}.

Record A_monotone_increasing_posg (S : Type) := {
  A_miposg_eqv          : A_eqv S 
; A_miposg_lte          : brel S 
; A_miposg_times        : binary_op S 
; A_miposg_lte_proofs   : po_proofs S (A_eqv_eq S A_miposg_eqv) A_miposg_lte
; A_miposg_times_proofs : msg_proofs S (A_eqv_eq S A_miposg_eqv) A_miposg_times
; A_miposg_top_bottom   : os_bottom_top_proofs S (A_eqv_eq S A_miposg_eqv) A_miposg_lte A_miposg_times                                    
; A_miposg_proofs       : os_monotone_increasing_proofs S A_miposg_lte A_miposg_times 
; A_miposg_ast          : cas_ast
}.

Record A_bounded_monotone_increasing_posg (S : Type) := {
  A_bmiposg_eqv          : A_eqv S 
; A_bmiposg_lte          : brel S 
; A_bmiposg_times        : binary_op S 
; A_bmiposg_lte_proofs   : po_proofs S (A_eqv_eq S A_bmiposg_eqv) A_bmiposg_lte
; A_bmiposg_times_proofs : msg_proofs S (A_eqv_eq S A_bmiposg_eqv) A_bmiposg_times
; A_bmiposg_top_bottom   : os_bounded_proofs S (A_eqv_eq S A_bmiposg_eqv) A_bmiposg_lte A_bmiposg_times                                    
; A_bmiposg_proofs       : os_monotone_increasing_proofs S A_bmiposg_lte A_bmiposg_times 
; A_bmiposg_ast          : cas_ast
}.

Record A_monotone_striclty_increasing_posg (S : Type) := {
  A_msiposg_eqv          : A_eqv S 
; A_msiposg_lte          : brel S 
; A_msiposg_times        : binary_op S 
; A_msiposg_lte_proofs   : po_proofs S (A_eqv_eq S A_msiposg_eqv) A_msiposg_lte
; A_msiposg_times_proofs : msg_proofs S (A_eqv_eq S A_msiposg_eqv) A_msiposg_times
; A_msiposg_top_bottom   : os_bottom_top_proofs S (A_eqv_eq S A_msiposg_eqv) A_msiposg_lte A_msiposg_times                                    
; A_msiposg_proofs       : os_monotone_strictly_increasing_proofs S A_msiposg_lte A_msiposg_times 
; A_msiposg_ast          : cas_ast
}.

Record A_meet_semilattice {S : Type} := {
  A_msl_eqv           : A_eqv S 
; A_msl_lte           : brel S 
; A_msl_meet          : binary_op S 
; A_msl_proofs        : meet_semilattice_proofs (A_eqv_eq S A_msl_eqv) A_msl_lte A_msl_meet
; A_msl_ast           : cas_ast
                                       }.

Record A_join_semilattice {S : Type} := {
  A_jsl_eqv           : A_eqv S 
; A_jsl_lte           : brel S 
; A_jsl_join          : binary_op S 
; A_jsl_proofs        : join_semilattice_proofs (A_eqv_eq S A_jsl_eqv) A_jsl_lte A_jsl_join
; A_jsl_ast           : cas_ast
}.

End ACAS.
