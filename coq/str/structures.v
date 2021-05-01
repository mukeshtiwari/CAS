Require Import CAS.coq.theory.facts. (* for witness functions.  move these? *)
Require Import CAS.coq.tr.structures. 

Record os_proofs (S: Type) (lte : brel S) (times : binary_op S) := 
{
  A_os_left_monotonic_d      : os_left_monotone_decidable S lte times 
; A_os_right_monotonic_d     : os_left_monotone_decidable S lte times 

; A_os_left_increasing_d     : os_left_increasing_decidable S lte times 
; A_os_right_increasing_d    : os_right_increasing_decidable S lte times 

}. 

(* transforms *)

Record sltr_proofs (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) :=
{
  sltr_distributive_d : sltr_distributive_decidable S L r add ltr
; sltr_absorptive_d   : sltr_absorptive_decidable S L r add ltr                                  
}.


Record A_sltr_CS (S L : Type) :=
{
  A_sltr_CS_carrier      : A_eqv S
; A_sltr_CS_label        : A_eqv L
; A_sltr_CS_plus         : binary_op S                                               
; A_sltr_CS_trans        : left_transform L S (* L -> (S -> S) *)
; A_sltr_CS_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_sltr_CS_carrier) A_sltr_CS_plus                                 
; A_sltr_CS_trans_proofs : ltr_proofs S L (A_eqv_eq S A_sltr_CS_carrier) (A_eqv_eq L A_sltr_CS_label)  A_sltr_CS_trans
; A_sltr_CS_proofs       : sltr_proofs S L (A_eqv_eq S A_sltr_CS_carrier) A_sltr_CS_plus A_sltr_CS_trans                                  
; A_sltr_CS_ast          : cas_ast
}.

Record A_sltr_CI (S L : Type) :=
{
  A_sltr_CI_carrier      : A_eqv S
; A_sltr_CI_label        : A_eqv L
; A_sltr_CI_plus         : binary_op S                                               
; A_sltr_CI_trans        : left_transform L S (* L -> (S -> S) *)
; A_sltr_CI_plus_proofs  : sg_CI_proofs S (A_eqv_eq S A_sltr_CI_carrier) A_sltr_CI_plus                                 
; A_sltr_CI_trans_proofs : ltr_proofs S L (A_eqv_eq S A_sltr_CI_carrier) (A_eqv_eq L A_sltr_CI_label)  A_sltr_CI_trans
; A_sltr_CI_proofs       : sltr_proofs S L (A_eqv_eq S A_sltr_CI_carrier) A_sltr_CI_plus A_sltr_CI_trans                                  
; A_sltr_CI_ast          : cas_ast 
}.



