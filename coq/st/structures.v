Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast. 
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.sg.structures. 
Require Import CAS.coq.tr.structures.

Require Import CAS.coq.st.properties. 


Record slt_proofs (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) :=
{
  slt_distributive_d : slt_distributive_decidable L S r add ltr
; slt_absorptive_d   : slt_absorptive_decidable L S r add ltr                                  
}.


Record A_slt_CS (L S : Type) :=
{
  A_slt_CS_carrier      : A_eqv S
; A_slt_CS_label        : A_eqv L
; A_slt_CS_plus         : binary_op S                                               
; A_slt_CS_trans        : left_transform L S (* L -> (S -> S) *)
; A_slt_CS_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_slt_CS_carrier) A_slt_CS_plus                                 
; A_slt_CS_trans_proofs : ltr_proofs L S (A_eqv_eq S A_slt_CS_carrier) (A_eqv_eq L A_slt_CS_label)  A_slt_CS_trans
; A_slt_CS_proofs       : slt_proofs L S (A_eqv_eq S A_slt_CS_carrier) A_slt_CS_plus A_slt_CS_trans                                  
; A_slt_CS_ast          : cas_ast
}.

Record A_slt_CI (L S : Type) :=
{
  A_slt_CI_carrier      : A_eqv S
; A_slt_CI_label        : A_eqv L
; A_slt_CI_plus         : binary_op S                                               
; A_slt_CI_trans        : left_transform L S (* L -> (S -> S) *)
; A_slt_CI_plus_proofs  : sg_CI_proofs S (A_eqv_eq S A_slt_CI_carrier) A_slt_CI_plus                                 
; A_slt_CI_trans_proofs : ltr_proofs L S (A_eqv_eq S A_slt_CI_carrier) (A_eqv_eq L A_slt_CI_label)  A_slt_CI_trans
; A_slt_CI_proofs       : slt_proofs L S (A_eqv_eq S A_slt_CI_carrier) A_slt_CI_plus A_slt_CI_trans                                  
; A_slt_CI_ast          : cas_ast 
}.



