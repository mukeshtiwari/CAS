Require Import CAS.code.basic_types. 
Require Import CAS.theory.properties.

(* eqv *) 
Record eqv_proofs (S : Type) (eq : brel S) := {
  A_eqv_nontrivial  : brel_nontrivial S eq          
; A_eqv_congruence  : brel_congruence S eq eq  
; A_eqv_reflexive   : brel_reflexive S eq            
; A_eqv_transitive  : brel_transitive S eq           
; A_eqv_symmetric   : brel_symmetric S eq            
}.

(* orders *) 

(* quasi-order *) 
Record qo_proofs (S : Type) (eq qo : brel S) := {
  A_qo_congruence      : brel_congruence S eq qo 
; A_qo_reflexive       : brel_reflexive S qo            
; A_qo_transitive      : brel_transitive S qo           
; A_qo_antisymmetric_d : brel_antisymmetric_decidable S eq qo 
; A_qo_total_d         : brel_total_decidable S qo           
}.

(* partial-order *) 
Record po_proofs (S : Type) (eq po : brel S) := {
  A_po_congruence    : brel_congruence S eq po 
; A_po_reflexive     : brel_reflexive S po            
; A_po_transitive    : brel_transitive S po           
; A_po_antisymmetric : brel_antisymmetric S eq po 
; A_po_total_d       : brel_total_decidable S po           
}.

(* total-order *) 
Record to_proofs (S : Type) (eq po : brel S) := {
  A_to_congruence    : brel_congruence S eq po 
; A_to_reflexive     : brel_reflexive S po            
; A_to_transitive    : brel_transitive S po           
; A_to_antisymmetric : brel_antisymmetric S eq po 
; A_to_total         : brel_total S po           
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

(* needed to decide distributivity of lex     *) 
; A_sg_left_cancel_d    : bop_left_cancellative_decidable S eq bop 
; A_sg_right_cancel_d   : bop_right_cancellative_decidable S eq bop 

(* needed to decide distributivity of lex     *) 
; A_sg_left_constant_d  : bop_left_constant_decidable S eq bop 
; A_sg_right_constant_d : bop_right_constant_decidable S eq bop 

(* needed to decide absorptivity of lex      *) 
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

(* order semigroups 

Record bs_proofs (S: Type) (eq : brel S) (lte : brel S) (times : binary_op S) := 
{
  A_os_left_monotonic_d      : bop_left_distributive_decidable S eq plus times 
; A_os_right_monotonic_d     : bop_right_distributive_decidable S eq plus times 

; A_os_plus_id_is_times_ann_d   : bops_id_equals_ann_decidable S eq plus times 
; A_os_times_id_is_plus_ann_d   : bops_id_equals_ann_decidable S eq times plus 

; A_bs_left_left_absorptive_d   : bops_left_left_absorptive_decidable S eq plus times 
; A_bs_left_right_absorptive_d  : bops_left_right_absorptive_decidable S eq plus times 
; A_bs_right_left_absorptive_d  : bops_right_left_absorptive_decidable S eq plus times 
; A_bs_right_right_absorptive_d : bops_right_right_absorptive_decidable S eq plus times 



}. 
*)