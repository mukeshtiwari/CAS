Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.brel.eq_nat. 
Require Import CAS.theory.bop.min.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cas.brel.eqv_nat. 
Require Import CAS.theory.facts. 

Definition sg_proofs_min : sg_proofs nat brel_eq_nat bop_min := 
{| 
  A_sg_associative   := bop_min_associative
; A_sg_congruence    := bop_min_congruence
; A_sg_commutative_d := inl _ bop_min_commutative
; A_sg_selective_d   := inl _ bop_min_selective
; A_sg_idempotent_d  := inl _ (bop_selective_implies_idempotent nat brel_eq_nat bop_min  
                                 bop_min_selective)
; A_sg_exists_id_d  := inr _ bop_min_not_exists_id
; A_sg_exists_ann_d  := inl _ bop_min_exists_ann 

; A_sg_is_left_d     := inr _ (bop_commutative_implies_not_is_left nat brel_eq_nat bop_min  
                                     brel_eq_nat_nontrivial
                                     brel_eq_nat_symmetric
                                     brel_eq_nat_transitive 
                                     bop_min_commutative)
; A_sg_is_right_d   := inr _ (bop_commutative_implies_not_is_right nat brel_eq_nat bop_min  
                                     brel_eq_nat_nontrivial
                                     brel_eq_nat_symmetric
                                     brel_eq_nat_transitive 
                                     bop_min_commutative)

; A_sg_left_cancel_d := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative nat brel_eq_nat bop_min  
                                       brel_eq_nat_congruence 
                                       brel_eq_nat_nontrivial
                                       brel_eq_nat_reflexive 
                                       brel_eq_nat_symmetric
                                       brel_eq_nat_transitive 
                                       bop_min_associative
                                       bop_min_congruence 
                                       (bop_selective_implies_idempotent nat brel_eq_nat bop_min  
                                            bop_min_selective)
                                       bop_min_commutative
                                       (inl _ bop_min_selective)
                                   )
; A_sg_right_cancel_d := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_right_cancellative nat brel_eq_nat bop_min  
                                       brel_eq_nat_congruence 
                                       brel_eq_nat_nontrivial
                                       brel_eq_nat_reflexive 
                                       brel_eq_nat_symmetric
                                       brel_eq_nat_transitive 
                                       bop_min_associative
                                       bop_min_congruence 
                                       (bop_selective_implies_idempotent nat brel_eq_nat bop_min  
                                            bop_min_selective)
                                       bop_min_commutative
                                       (inl _ bop_min_selective)
                                   )
; A_sg_left_constant_d := inr _ (bop_idempotent_and_commutative_imply_not_left_constant nat brel_eq_nat bop_min  
                                       brel_eq_nat_nontrivial
                                       brel_eq_nat_congruence 
                                       brel_eq_nat_reflexive 
                                       brel_eq_nat_transitive
                                       (bop_selective_implies_idempotent nat brel_eq_nat bop_min  
                                            bop_min_selective) 
                                       bop_min_commutative
                                   ) 
; A_sg_right_constant_d := inr _ (bop_idempotent_and_commutative_imply_not_right_constant nat brel_eq_nat bop_min  
                                       brel_eq_nat_nontrivial
                                       brel_eq_nat_congruence 
                                       brel_eq_nat_reflexive 
                                       brel_eq_nat_symmetric
                                       brel_eq_nat_transitive
                                       (bop_selective_implies_idempotent nat brel_eq_nat bop_min  
                                            bop_min_selective) 
                                       bop_min_commutative
                                   ) 
; A_sg_anti_left_d      := inr _ (bop_idempotent_implies_not_anti_left nat brel_eq_nat bop_min  
                                       (brel_nontrivial_witness nat brel_eq_nat brel_eq_nat_nontrivial) 
                                       brel_eq_nat_symmetric
                                       (bop_selective_implies_idempotent nat brel_eq_nat bop_min  
                                            bop_min_selective) 
                                   )
; A_sg_anti_right_d     := inr _ (bop_idempotent_implies_not_anti_right nat brel_eq_nat bop_min  
                                       (brel_nontrivial_witness nat brel_eq_nat brel_eq_nat_nontrivial) 
                                       brel_eq_nat_symmetric
                                       (bop_selective_implies_idempotent nat brel_eq_nat bop_min  
                                            bop_min_selective) 
                                   )

|}. 

Definition A_sg_min : A_sg nat 
:= {| 
     A_sg_eq          := A_eqv_eq_nat 
   ; A_sg_bop         := bop_min 
   ; A_sg_proofs      := sg_proofs_min 
   ; A_sg_ast         := Ast_sg_min 
   |}. 
