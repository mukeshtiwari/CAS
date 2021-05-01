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


(* hack? *) 
Record top_bottom_ann_id_with_id_proofs (S: Type) (eq lte : brel S) (times : binary_op S) := 
{
  A_top_ann_d : os_top_equals_ann_decidable S eq lte times 
; A_bottom_id : os_bottom_equals_id S eq lte times 
}.


(* hack? *) 
Record monotone_os_proofs (S: Type) (lte : brel S) (times : binary_op S) := 
{
  A_mos_left_monotonic      : os_left_monotone S lte times 
; A_mos_right_monotonic     : os_right_monotone S lte times 

; A_mos_left_increasing_d     : os_left_increasing_decidable S lte times 
; A_mos_right_increasing_d    : os_right_increasing_decidable S lte times 

}. 


Record A_monotone_posg (S : Type) := {
  A_mposg_eqv          : A_eqv S 
; A_mposg_lte          : brel S 
; A_mposg_times        : binary_op S 
; A_mposg_lte_proofs   : po_proofs S (A_eqv_eq S A_mposg_eqv) A_mposg_lte
; A_mposg_times_proofs : msg_proofs S (A_eqv_eq S A_mposg_eqv) A_mposg_times
; A_mposg_top_bottom   : top_bottom_ann_id_with_id_proofs S (A_eqv_eq S A_mposg_eqv) A_mposg_lte A_mposg_times                                    
; A_mposg_proofs       : monotone_os_proofs S A_mposg_lte A_mposg_times 
; A_mposg_ast          : cas_ast
}.



Record posg_top_bottom_id_ann_proofs (S: Type) (eq lte : brel S) (times : binary_op S) := 
{
  A_posg_bottom   : brel_exists_qo_bottom S eq lte
; A_posg_top_d    : brel_exists_qo_top_decidable S eq lte
; A_posg_id_d     : bop_exists_id_decidable S eq times
; A_posg_ann_d    : bop_exists_ann_decidable S eq times 
; A_posg_bottom_equals_id_d : os_bottom_equals_id_decidable S eq lte times 
; A_posg_top_equals_ann_d   : os_top_equals_ann_decidable S eq lte times 
}.


Record posg_proofs (S: Type) (lte : brel S) (times : binary_op S) := 
{
  A_posg_left_monotonic_d      : os_left_monotone_decidable S lte times 
; A_posg_right_monotonic_d     : os_left_monotone_decidable S lte times 

; A_posg_left_increasing_d     : os_left_increasing_decidable S lte times 
; A_posg_right_increasing_d    : os_right_increasing_decidable S lte times 

; A_posg_left_strictly_increasing_d     : os_left_strictly_increasing_decidable S lte times 
; A_posg_right_strictly_increasing_d    : os_right_strictly_increasing_decidable S lte times 
}. 

Record A_posg (S : Type) := {
  A_posg_eqv          : A_eqv S 
; A_posg_lte          : brel S 
; A_posg_times        : binary_op S 
; A_posg_lte_proofs   : po_proofs S (A_eqv_eq S A_posg_eqv) A_posg_lte
; A_posg_times_proofs : sg_proofs S (A_eqv_eq S A_posg_eqv) A_posg_times
; A_posg_top_bottom_proofs : posg_top_bottom_id_ann_proofs S (A_eqv_eq S A_posg_eqv) A_posg_lte A_posg_times
; A_posg_proofs       : posg_proofs S A_posg_lte A_posg_times 
; A_posg_ast          : cas_ast
}.

