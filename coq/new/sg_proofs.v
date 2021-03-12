Require Import CAS.coq.common.compute. 
Require Import CAS.coq.common.sg_certificates.
Require Import CAS.coq.common.bop_properties. 



Record sg_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
(* "root set" required                          *) 
  A_sg_associative      : bop_associative S eq bop 
; A_sg_congruence       : bop_congruence S eq bop   

(* "root set" of optional semigroup properties *) 
; A_sg_commutative_d    : bop_commutative_decidable S eq bop  
; A_sg_selective_d      : bop_selective_decidable S eq bop  
; A_sg_idempotent_d     : bop_idempotent_decidable S eq bop  

(* needed to decide selectivity of product    *) 
; A_sg_is_left_d        : bop_is_left_decidable S eq bop  
; A_sg_is_right_d       : bop_is_right_decidable S eq bop  

(* needed to decide distributivity of (lex, product), on mult-part *) 
; A_sg_left_cancel_d    : bop_left_cancellative_decidable S eq bop 
; A_sg_right_cancel_d   : bop_right_cancellative_decidable S eq bop 

(* needed to decide distributivity of (lex, product, on mult-part *) 
; A_sg_left_constant_d  : bop_left_constant_decidable S eq bop 
; A_sg_right_constant_d : bop_right_constant_decidable S eq bop 

(* needed to decide absorptivity of (lex, product), on mult-part*) 
; A_sg_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_sg_anti_right_d     : bop_anti_right_decidable S eq bop 
}. 

(* multiplicative semigroup *) 
Record msg_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_msg_associative      : bop_associative S eq bop 
; A_msg_congruence       : bop_congruence S eq bop   
; A_msg_commutative_d    : bop_commutative_decidable S eq bop  

(* needed?*)                                                    
; A_msg_is_left_d        : bop_is_left_decidable S eq bop  
; A_msg_is_right_d       : bop_is_right_decidable S eq bop  

(***)                                                   
; A_msg_left_cancel_d    : bop_left_cancellative_decidable S eq bop 
; A_msg_right_cancel_d   : bop_right_cancellative_decidable S eq bop 

; A_msg_left_constant_d  : bop_left_constant_decidable S eq bop 
; A_msg_right_constant_d : bop_right_constant_decidable S eq bop 

; A_msg_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_msg_anti_right_d     : bop_anti_right_decidable S eq bop 
}. 

