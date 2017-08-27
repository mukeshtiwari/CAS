Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.brel.eq_bool. 
Require Import CAS.theory.bop.or.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cas.brel.eqv_bool. 
Require Import CAS.theory.facts. 

Definition sg_proofs_or : sg_proofs bool brel_eq_bool bop_or := 
{| 
  A_sg_associative   := bop_or_associative
; A_sg_congruence    := bop_or_congruence
; A_sg_commutative_d := inl _ bop_or_commutative
; A_sg_selective_d   := inl _ bop_or_selective
; A_sg_idempotent_d  := inl _ (bop_selective_implies_idempotent bool brel_eq_bool bop_or  
                                 bop_or_selective)
; A_sg_exists_id_d   := inl _ bop_or_exists_id 
; A_sg_exists_ann_d  := inl _ bop_or_exists_ann 

; A_sg_is_left_d     := inr _ (bop_commutative_implies_not_is_left bool brel_eq_bool bop_or  
                                     brel_eq_bool_nontrivial
                                     brel_eq_bool_symmetric
                                     brel_eq_bool_transitive 
                                     bop_or_commutative)
; A_sg_is_right_d   := inr _ (bop_commutative_implies_not_is_right bool brel_eq_bool bop_or  
                                     brel_eq_bool_nontrivial
                                     brel_eq_bool_symmetric
                                     brel_eq_bool_transitive 
                                     bop_or_commutative)

; A_sg_left_cancel_d := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative bool brel_eq_bool bop_or  
                                       brel_eq_bool_congruence 
                                       brel_eq_bool_nontrivial
                                       brel_eq_bool_reflexive 
                                       brel_eq_bool_symmetric
                                       brel_eq_bool_transitive 
                                       bop_or_associative
                                       bop_or_congruence 
                                       (bop_selective_implies_idempotent bool brel_eq_bool bop_or  
                                            bop_or_selective)
                                       bop_or_commutative
                                       (inl _ bop_or_selective)
                                   )
; A_sg_right_cancel_d := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_right_cancellative bool brel_eq_bool bop_or  
                                       brel_eq_bool_congruence 
                                       brel_eq_bool_nontrivial
                                       brel_eq_bool_reflexive 
                                       brel_eq_bool_symmetric
                                       brel_eq_bool_transitive 
                                       bop_or_associative
                                       bop_or_congruence 
                                       (bop_selective_implies_idempotent bool brel_eq_bool bop_or  
                                            bop_or_selective)
                                       bop_or_commutative
                                       (inl _ bop_or_selective)
                                   )
; A_sg_left_constant_d := inr _ (bop_idempotent_and_commutative_imply_not_left_constant bool brel_eq_bool bop_or  
                                       brel_eq_bool_nontrivial
                                       brel_eq_bool_congruence 
                                       brel_eq_bool_reflexive 
                                       brel_eq_bool_transitive
                                       (bop_selective_implies_idempotent bool brel_eq_bool bop_or  
                                            bop_or_selective) 
                                       bop_or_commutative
                                   ) 
; A_sg_right_constant_d := inr _ (bop_idempotent_and_commutative_imply_not_right_constant bool brel_eq_bool bop_or  
                                       brel_eq_bool_nontrivial
                                       brel_eq_bool_congruence 
                                       brel_eq_bool_reflexive 
                                       brel_eq_bool_symmetric
                                       brel_eq_bool_transitive
                                       (bop_selective_implies_idempotent bool brel_eq_bool bop_or  
                                            bop_or_selective) 
                                       bop_or_commutative
                                   ) 
; A_sg_anti_left_d      := inr _ (bop_idempotent_implies_not_anti_left bool brel_eq_bool bop_or  
                                       (brel_nontrivial_witness bool brel_eq_bool brel_eq_bool_nontrivial) 
                                       brel_eq_bool_symmetric
                                       (bop_selective_implies_idempotent bool brel_eq_bool bop_or  
                                            bop_or_selective) 
                                   )
; A_sg_anti_right_d     := inr _ (bop_idempotent_implies_not_anti_right bool brel_eq_bool bop_or  
                                       (brel_nontrivial_witness bool brel_eq_bool brel_eq_bool_nontrivial) 
                                       brel_eq_bool_symmetric
                                       (bop_selective_implies_idempotent bool brel_eq_bool bop_or  
                                            bop_or_selective) 
                                   )

|}. 



Definition A_sg_or : A_sg bool
:= {| 
     A_sg_eq          := A_eqv_bool
   ; A_sg_bop         := bop_or
   ; A_sg_proofs      := sg_proofs_or
   ; A_sg_ast         := Ast_sg_or 
   |}. 
