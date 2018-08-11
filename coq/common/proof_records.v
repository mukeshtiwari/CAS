Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.brel_properties.
Require Import CAS.coq.common.uop_properties.
Require Import CAS.coq.common.bop_properties.
Require Import CAS.coq.common.bs_properties.
Require Import CAS.coq.common.os_properties.
Require Import CAS.coq.theory.facts. (* for witness functions.  move these? *) 
(* eqv *) 
(*
Record eqv_proofs (S : Type) (eq : brel S) (rep : unary_op S) := 
*) 
Record eqv_proofs (S : Type) (eq : brel S) := 
{
(*
; A_eqv_rep_correct    : brel_rep_correct S eq rep
; A_eqv_rep_idempotent : brel_rep_idempotent S eq rep  
*) 
  A_eqv_congruence     : brel_congruence S eq eq  
; A_eqv_reflexive      : brel_reflexive S eq            
; A_eqv_transitive     : brel_transitive S eq           
; A_eqv_symmetric      : brel_symmetric S eq            
}.

(*
Definition eqv_get_witness_element (S : Type) (eq : brel S) : (eqv_proofs S eq) -> S
:= λ eqv, brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqv). 
*) 
(* orders *) 

(* quasi-order *) 
Record qo_proofs (S : Type) (eq qo : brel S) := {
  A_qo_congruence      : brel_congruence S eq qo 
; A_qo_reflexive       : brel_reflexive S qo            
; A_qo_transitive      : brel_transitive S qo           
; A_qo_antisymmetric_d : brel_antisymmetric_decidable S eq qo 
; A_qo_total_d         : brel_total_decidable S qo           
; A_qo_exists_top_d    : brel_exists_top_decidable S qo           
; A_qo_exists_bottom_d : brel_exists_bottom_decidable S qo           
}.

(* partial-order *) 
Record po_proofs (S : Type) (eq po : brel S) := {
  A_po_congruence    : brel_congruence S eq po 
; A_po_reflexive     : brel_reflexive S po            
; A_po_transitive    : brel_transitive S po           
; A_po_antisymmetric : brel_antisymmetric S eq po 
; A_po_total_d       : brel_total_decidable S po           
; A_po_exists_top_d    : brel_exists_top_decidable S po           
; A_po_exists_bottom_d : brel_exists_bottom_decidable S po           
}.

(* total-order *) 
Record to_proofs (S : Type) (eq po : brel S) := {
  A_to_congruence    : brel_congruence S eq po 
; A_to_reflexive     : brel_reflexive S po            
; A_to_transitive    : brel_transitive S po           
; A_to_antisymmetric : brel_antisymmetric S eq po 
; A_to_total         : brel_total S po           
; A_to_exists_top_d    : brel_exists_top_decidable S po           
; A_to_exists_bottom_d : brel_exists_bottom_decidable S po           
}.


(* semigroups *) 

Record sg_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
(* "root set" required                          *) 
  A_sg_associative      : bop_associative S eq bop 
; A_sg_congruence       : bop_congruence S eq bop   

(* "root set" of optional semigroup properties *) 
; A_sg_commutative_d    : bop_commutative_decidable S eq bop  
; A_sg_selective_d      : bop_selective_decidable S eq bop  
; A_sg_idempotent_d     : bop_idempotent_decidable S eq bop  
; A_sg_exists_id_d      : bop_exists_id_decidable S eq bop 
; A_sg_exists_ann_d     : bop_exists_ann_decidable S eq bop 

(* needed to decide selectivity of product    *) 
; A_sg_is_left_d        : bop_is_left_decidable S eq bop  
; A_sg_is_right_d       : bop_is_right_decidable S eq bop  

(* needed to decide distributivity of (lex, product)     *) 
; A_sg_left_cancel_d    : bop_left_cancellative_decidable S eq bop 
; A_sg_right_cancel_d   : bop_right_cancellative_decidable S eq bop 

(* needed to decide distributivity of (lex, product     *) 
; A_sg_left_constant_d  : bop_left_constant_decidable S eq bop 
; A_sg_right_constant_d : bop_right_constant_decidable S eq bop 

(* needed to decide absorptivity of (lex, product)      *) 
; A_sg_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_sg_anti_right_d     : bop_anti_right_decidable S eq bop 
}. 


Record sg_C_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_C_associative      : bop_associative S eq bop 
; A_sg_C_congruence       : bop_congruence S eq bop   
; A_sg_C_commutative      : bop_commutative S eq bop  

; A_sg_C_selective_d      : bop_selective_decidable S eq bop  
; A_sg_C_idempotent_d     : bop_idempotent_decidable S eq bop  
; A_sg_C_exists_id_d      : bop_exists_id_decidable S eq bop 
; A_sg_C_exists_ann_d     : bop_exists_ann_decidable S eq bop 

; A_sg_C_left_cancel_d    : bop_left_cancellative_decidable S eq bop 
; A_sg_C_right_cancel_d   : bop_right_cancellative_decidable S eq bop 

; A_sg_C_left_constant_d  : bop_left_constant_decidable S eq bop 
; A_sg_C_right_constant_d : bop_right_constant_decidable S eq bop 

; A_sg_C_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_sg_C_anti_right_d     : bop_anti_right_decidable S eq bop 
}. 


Record sg_CS_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_CS_associative        : bop_associative S eq bop 
; A_sg_CS_congruence         : bop_congruence S eq bop   
; A_sg_CS_commutative        : bop_commutative S eq bop  
; A_sg_CS_selective          : bop_selective S eq bop  

; A_sg_CS_exists_id_d        : bop_exists_id_decidable S eq bop 
; A_sg_CS_exists_ann_d       : bop_exists_ann_decidable S eq bop 
}. 

Record sg_CI_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_CI_associative        : bop_associative S eq bop 
; A_sg_CI_congruence         : bop_congruence S eq bop   
; A_sg_CI_commutative        : bop_commutative S eq bop  
; A_sg_CI_idempotent         : bop_idempotent S eq bop  

; A_sg_CI_selective_d        : bop_selective_decidable S eq bop  
; A_sg_CI_exists_id_d        : bop_exists_id_decidable S eq bop 
; A_sg_CI_exists_ann_d       : bop_exists_ann_decidable S eq bop 
}. 

Record sg_CK_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_CK_associative        : bop_associative S eq bop 
; A_sg_CK_congruence         : bop_congruence S eq bop   
; A_sg_CK_commutative        : bop_commutative S eq bop  
; A_sg_CK_left_cancel        : bop_left_cancellative S eq bop  

; A_sg_CK_exists_id_d        : bop_exists_id_decidable S eq bop 
; A_sg_CK_anti_left_d        : bop_anti_left_decidable S eq bop 
; A_sg_CK_anti_right_d       : bop_anti_right_decidable S eq bop 
}. 

(* bs = bi-semigroup *) 

Record bs_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_bs_left_distributive_d      : bop_left_distributive_decidable S eq plus times 
; A_bs_right_distributive_d     : bop_right_distributive_decidable S eq plus times 

; A_bs_plus_id_is_times_ann_d   : bops_id_equals_ann_decidable S eq plus times 
; A_bs_times_id_is_plus_ann_d   : bops_id_equals_ann_decidable S eq times plus 

; A_bs_left_left_absorptive_d   : bops_left_left_absorptive_decidable S eq plus times 
; A_bs_left_right_absorptive_d  : bops_left_right_absorptive_decidable S eq plus times 
; A_bs_right_left_absorptive_d  : bops_right_left_absorptive_decidable S eq plus times 
; A_bs_right_right_absorptive_d : bops_right_right_absorptive_decidable S eq plus times 

}.

Record semiring_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_semiring_left_distributive      : bop_left_distributive S eq plus times 
; A_semiring_right_distributive     : bop_right_distributive S eq plus times 

; A_semiring_plus_id_is_times_ann_d   : bops_id_equals_ann_decidable S eq plus times 
; A_semiring_times_id_is_plus_ann_d   : bops_id_equals_ann_decidable S eq times plus
                                                                     
; A_semiring_left_left_absorptive_d   : bops_left_left_absorptive_decidable S eq plus times 
; A_semiring_left_right_absorptive_d  : bops_left_right_absorptive_decidable S eq plus times 
}.

Record lattice_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_lattice_absorptive      : bops_left_left_absorptive S eq plus times
; A_lattice_absorptive_dual : bops_left_left_absorptive S eq times plus
 
; A_lattice_distributive_d       : bop_left_distributive_decidable S eq plus times
; A_lattice_distributive_dual_d  : bop_left_distributive_decidable S eq times plus (* required for lattice_dual  ? *)
}. 


Record distributive_lattice_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_distributive_lattice_absorptive        : bops_left_left_absorptive S eq plus times
; A_distributive_lattice_absorptive_dual   : bops_left_left_absorptive S eq times plus
; A_distributive_lattice_distributive      : bop_left_distributive S eq plus times
(*                                                                   
; A_distributive_lattice_distributive_dual : bop_left_distributive S eq times plus (* could be derived, but here for convenience *)                          
*)
}. 



(* order semigroups *) 

Record os_proofs (S: Type) (lte : brel S) (times : binary_op S) := 
{
  A_os_left_monotonic_d      : os_left_monotone_decidable S lte times 
; A_os_right_monotonic_d     : os_left_monotone_decidable S lte times 

; A_os_left_increasing_d     : os_left_increasing_decidable S lte times 
; A_os_right_increasing_d    : os_right_increasing_decidable S lte times 

}. 
