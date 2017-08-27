Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.

Require Import CAS.theory.facts. 


Definition A_sg_proofs_from_sg_C_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), eqv_proofs S r -> sg_C_proofs S r b -> sg_proofs S r b 
:= λ S r b eqvS sgS, 
{|
  A_sg_associative      := A_sg_C_associative S r b sgS 
; A_sg_congruence       := A_sg_C_congruence S r b sgS 
; A_sg_commutative_d    := inl _ (A_sg_C_commutative S r b sgS) 
; A_sg_selective_d      := A_sg_C_selective_d S r b sgS    
; A_sg_is_left_d        := inr _ (bop_commutative_implies_not_is_left S r b 
                                     (A_eqv_nontrivial S r eqvS) 
                                     (A_eqv_symmetric S r eqvS) 
                                     (A_eqv_transitive S r eqvS) 
                                     (A_sg_C_commutative S r b sgS))
; A_sg_is_right_d       := inr _ (bop_commutative_implies_not_is_right S r b 
                                     (A_eqv_nontrivial S r eqvS) 
                                     (A_eqv_symmetric S r eqvS) 
                                     (A_eqv_transitive S r eqvS) 
                                     (A_sg_C_commutative S r b sgS))
; A_sg_idempotent_d     := A_sg_C_idempotent_d S r b sgS    
; A_sg_exists_id_d      := A_sg_C_exists_id_d S r b sgS    
; A_sg_exists_ann_d     := A_sg_C_exists_ann_d S r b sgS    
; A_sg_left_cancel_d    := A_sg_C_left_cancel_d S r b sgS    
; A_sg_right_cancel_d   := A_sg_C_right_cancel_d S r b sgS    
; A_sg_left_constant_d  := A_sg_C_left_constant_d S r b sgS
; A_sg_right_constant_d := A_sg_C_right_constant_d S r b sgS
; A_sg_anti_left_d      := A_sg_C_anti_left_d S r b sgS
; A_sg_anti_right_d     := A_sg_C_anti_right_d S r b sgS
|}. 

Definition A_sg_from_sg_C : ∀ (S : Type),  A_sg_C S -> A_sg S 
:= λ S sgS, 
   {| 
     A_sg_eq          := A_sg_C_eqv S sgS
   ; A_sg_bop         := A_sg_C_bop S sgS
   ; A_sg_proofs      := A_sg_proofs_from_sg_C_proofs S 
                            (A_eqv_eq S (A_sg_C_eqv S sgS)) 
                            (A_sg_C_bop S sgS) 
                            (A_eqv_proofs S (A_sg_C_eqv S sgS)) 
                            (A_sg_C_proofs S sgS) 
   ; A_sg_ast        := Ast_sg_from_sg_C (A_sg_C_ast S sgS)
   |}. 

 

Definition A_sg_C_proofs_from_sg_CI_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), eqv_proofs S r -> sg_CI_proofs S r b -> sg_C_proofs S r b 
:= λ S r b eqvS sgS, 
{|
  A_sg_C_associative      := A_sg_CI_associative S r b sgS 
; A_sg_C_congruence       := A_sg_CI_congruence S r b sgS 
; A_sg_C_commutative      := A_sg_CI_commutative S r b sgS
; A_sg_C_selective_d      := A_sg_CI_selective_d S r b sgS    
; A_sg_C_idempotent_d     := inl _ (A_sg_CI_idempotent S r b sgS) 
; A_sg_C_exists_id_d      := A_sg_CI_exists_id_d S r b sgS    
; A_sg_C_exists_ann_d     := A_sg_CI_exists_ann_d S r b sgS    
; A_sg_C_left_cancel_d    := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative S r b 
                                       (A_eqv_congruence  S r eqvS) 
                                       (A_eqv_nontrivial S r eqvS) 
                                       (A_eqv_reflexive S r eqvS) 
                                       (A_eqv_symmetric S r eqvS) 
                                       (A_eqv_transitive S r eqvS) 
                                       (A_sg_CI_associative S r b sgS)
                                       (A_sg_CI_congruence S r b sgS)
                                       (A_sg_CI_idempotent S r b sgS)
                                       (A_sg_CI_commutative S r b sgS)
                                       (A_sg_CI_selective_d S r b sgS)
                                   )
; A_sg_C_right_cancel_d   := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_right_cancellative S r b 
                                       (A_eqv_congruence  S r eqvS) 
                                       (A_eqv_nontrivial S r eqvS) 
                                       (A_eqv_reflexive S r eqvS) 
                                       (A_eqv_symmetric S r eqvS) 
                                       (A_eqv_transitive S r eqvS) 
                                       (A_sg_CI_associative S r b sgS)
                                       (A_sg_CI_congruence S r b sgS)
                                       (A_sg_CI_idempotent S r b sgS)
                                       (A_sg_CI_commutative S r b sgS)
                                       (A_sg_CI_selective_d S r b sgS)
                                   )
; A_sg_C_left_constant_d  := inr _ (bop_idempotent_and_commutative_imply_not_left_constant S r b
                                       (A_eqv_nontrivial S r eqvS) 
                                       (A_eqv_congruence  S r eqvS) 
                                       (A_eqv_reflexive S r eqvS) 
                                       (A_eqv_transitive S r eqvS) 
                                       (A_sg_CI_idempotent S r b sgS)
                                       (A_sg_CI_commutative S r b sgS)
                                   ) 
; A_sg_C_right_constant_d := inr _ (bop_idempotent_and_commutative_imply_not_right_constant S r b
                                       (A_eqv_nontrivial S r eqvS) 
                                       (A_eqv_congruence  S r eqvS) 
                                       (A_eqv_reflexive S r eqvS) 
                                       (A_eqv_symmetric S r eqvS) 
                                       (A_eqv_transitive S r eqvS) 
                                       (A_sg_CI_idempotent S r b sgS)
                                       (A_sg_CI_commutative S r b sgS)
                                   ) 
; A_sg_C_anti_left_d      := inr _ (bop_idempotent_implies_not_anti_left S r b
                                       (eqv_get_witness_element _ _ eqvS)                                                                                                                           (A_eqv_symmetric S r eqvS) 
                                       (A_sg_CI_idempotent S r b sgS)
                                   )
; A_sg_C_anti_right_d     := inr _ (bop_idempotent_implies_not_anti_right S r b
                                       (eqv_get_witness_element _ _ eqvS)                                                                          
                                       (A_eqv_symmetric S r eqvS) 
                                       (A_sg_CI_idempotent S r b sgS)
                                   )
|}. 


Definition A_sg_C_from_sg_CI: ∀ (S : Type),  A_sg_CI S -> A_sg_C S 
:= λ S sgS, 
   {| 
     A_sg_C_eqv         := A_sg_CI_eqv S sgS
   ; A_sg_C_bop         := A_sg_CI_bop S sgS
   ; A_sg_C_proofs      := A_sg_C_proofs_from_sg_CI_proofs S 
                            (A_eqv_eq S (A_sg_CI_eqv S sgS)) 
                            (A_sg_CI_bop S sgS) 
                            (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                            (A_sg_CI_proofs S sgS) 
   ; A_sg_C_ast        := Ast_sg_C_from_sg_CI (A_sg_CI_ast S sgS)
   |}. 


Definition A_sg_CI_proofs_from_sg_CS_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), sg_CS_proofs S r b -> sg_CI_proofs S r b 
:= λ S r b sg_CSS, 
{|
  A_sg_CI_associative        := A_sg_CS_associative S r b sg_CSS 
; A_sg_CI_congruence         := A_sg_CS_congruence S r b sg_CSS 
; A_sg_CI_commutative        := A_sg_CS_commutative S r b sg_CSS
; A_sg_CI_idempotent         := bop_selective_implies_idempotent S r b (A_sg_CS_selective S r b sg_CSS)
; A_sg_CI_selective_d        := inl _ (A_sg_CS_selective S r b sg_CSS) 
; A_sg_CI_exists_id_d        := A_sg_CS_exists_id_d S r b sg_CSS    
; A_sg_CI_exists_ann_d       := A_sg_CS_exists_ann_d S r b sg_CSS    
|}. 


Definition A_sg_CI_from_sg_CS: ∀ (S : Type),  A_sg_CS S -> A_sg_CI S 
:= λ S sgS, 
   {| 
     A_sg_CI_eqv         := A_sg_CS_eqv S sgS
   ; A_sg_CI_bop         := A_sg_CS_bop S sgS
   ; A_sg_CI_proofs      := A_sg_CI_proofs_from_sg_CS_proofs S 
                            (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                            (A_sg_CS_bop S sgS) 
                            (A_sg_CS_proofs S sgS) 
   ; A_sg_CI_ast        := Ast_sg_CI_from_sg_CS (A_sg_CS_ast S sgS)
   |}. 



Definition A_sg_C_proofs_from_sg_CK_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), eqv_proofs S r -> sg_CK_proofs S r b -> sg_C_proofs S r b 
:= λ S r b eqvS sgS, 
let right_cancel := bop_commutative_and_left_cancellative_imply_right_cancellative S r b 
                      (A_eqv_transitive S r eqvS) 
                      (A_sg_CK_commutative S r b sgS)
                      (A_sg_CK_left_cancel S r b sgS)    
in 
let not_idem := bop_cancellative_implies_not_idempotent S r b 
                   (A_eqv_nontrivial S r eqvS)
                   (A_eqv_reflexive S r eqvS)  
                   (A_eqv_symmetric S r eqvS) 
                   (A_eqv_transitive S r eqvS) 
                   (A_sg_CK_associative S r b sgS)
                   (A_sg_CK_congruence S r b sgS)
                   (A_sg_CK_left_cancel S r b sgS)    
                   right_cancel 
                   (A_sg_CK_exists_id_d S r b sgS)
in 
{|
  A_sg_C_associative      := A_sg_CK_associative S r b sgS 
; A_sg_C_congruence       := A_sg_CK_congruence S r b sgS 
; A_sg_C_commutative      := A_sg_CK_commutative S r b sgS
; A_sg_C_selective_d      := inr _ (bop_not_idempotent_implies_not_selective S r b not_idem)
; A_sg_C_idempotent_d     := inr _ not_idem 
; A_sg_C_exists_id_d      := A_sg_CK_exists_id_d S r b sgS    
; A_sg_C_exists_ann_d     := inr (bop_left_cancellative_implies_not_exists_ann S r b 
                                    (A_eqv_symmetric S r eqvS) 
                                    (A_eqv_transitive S r eqvS) 
                                    (A_eqv_nontrivial S r eqvS) 
                                    (A_sg_CK_left_cancel S r b sgS)    
                                 )
; A_sg_C_left_cancel_d    := inl _ (A_sg_CK_left_cancel S r b sgS)    
; A_sg_C_right_cancel_d   := inl _ right_cancel 
; A_sg_C_left_constant_d  := inr _ (bop_left_cancellative_implies_not_left_constant S r b 
                                       (A_eqv_nontrivial S r eqvS) 
                                       (A_sg_CK_left_cancel S r b sgS)    
                                   )
; A_sg_C_right_constant_d := inr _ (bop_right_cancellative_implies_not_right_constant S r b 
                                       (A_eqv_nontrivial S r eqvS) 
                                       right_cancel    
                                   )
; A_sg_C_anti_left_d      := A_sg_CK_anti_left_d S r b sgS 
; A_sg_C_anti_right_d     := A_sg_CK_anti_right_d S r b sgS
|}. 



Definition A_sg_C_from_sg_CK: ∀ (S : Type),  A_sg_CK S -> A_sg_C S 
:= λ S sgS, 
   {| 
     A_sg_C_eqv         := A_sg_CK_eqv S sgS
   ; A_sg_C_bop         := A_sg_CK_bop S sgS
   ; A_sg_C_proofs      := A_sg_C_proofs_from_sg_CK_proofs S 
                            (A_eqv_eq S (A_sg_CK_eqv S sgS)) 
                            (A_sg_CK_bop S sgS)  
                            (A_eqv_proofs S (A_sg_CK_eqv S sgS)) 
                            (A_sg_CK_proofs S sgS) 
   ; A_sg_C_ast        := Ast_sg_C_from_sg_CK (A_sg_CK_ast S sgS)
   |}. 




(* DERIVED UPCASTS *) 

Definition A_sg_from_sg_CI: ∀ (S : Type),  A_sg_CI S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CI S sgS).  

Definition A_sg_from_sg_CK: ∀ (S : Type),  A_sg_CK S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CK S sgS).  

Definition A_sg_C_from_sg_CS: ∀ (S : Type),  A_sg_CS S -> A_sg_C S 
:= λ S sgS, A_sg_C_from_sg_CI S (A_sg_CI_from_sg_CS S sgS ). 

Definition A_sg_from_sg_CS: ∀ (S : Type),  A_sg_CS S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CS S sgS).  


Definition A_sg_C_proofs_from_sg_CS_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S),  eqv_proofs S r -> sg_CS_proofs S r b -> sg_C_proofs S r b
:= λ S r b eqv sg_CS, A_sg_C_proofs_from_sg_CI_proofs S r b eqv 
                     (A_sg_CI_proofs_from_sg_CS_proofs S r b sg_CS ). 


Definition A_sg_proofs_from_sg_CS_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), eqv_proofs S r ->  sg_CS_proofs S r b -> sg_proofs S r b 
:= λ S r b eqv sg_CS, A_sg_proofs_from_sg_C_proofs S r b eqv (A_sg_C_proofs_from_sg_CS_proofs S r b eqv sg_CS).

