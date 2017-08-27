Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.bop.product. 
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cas.eqv.product.
Require Import CAS.theory.facts. 


Definition sg_proofs_product : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_proofs S rS bS -> 
     sg_proofs T rT bT -> 
        sg_proofs (S * T) (brel_product rS rT) (bop_product bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_associative   := bop_product_associative S T rS rT bS bT 
                         (A_sg_associative _ _ _ sgS) 
                         (A_sg_associative _ _ _ sgT) 
; A_sg_congruence    := bop_product_congruence S T rS rT bS bT 
                         (A_sg_congruence _ _ _ sgS) 
                         (A_sg_congruence _ _ _ sgT) 
; A_sg_commutative_d := bop_product_commutative_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_sg_commutative_d _ _ _ sgS) 
                         (A_sg_commutative_d _ _ _ sgT) 
; A_sg_selective_d   := bop_product_selective_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)                                                     
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_eqv_symmetric _ _ eqvT)
                         (A_eqv_transitive _ _ eqvT)
                         (A_sg_is_left_d _ _ _ sgS) 
                         (A_sg_is_left_d _ _ _ sgT) 
                         (A_sg_is_right_d _ _ _ sgS) 
                         (A_sg_is_right_d _ _ _ sgT) 
; A_sg_is_left_d     := bop_product_is_left_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_sg_is_left_d _ _ _ sgS) 
                         (A_sg_is_left_d _ _ _ sgT) 
; A_sg_is_right_d    := bop_product_is_right_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_sg_is_right_d _ _ _ sgS) 
                         (A_sg_is_right_d _ _ _ sgT) 
; A_sg_idempotent_d  := bop_product_idempotent_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_sg_idempotent_d _ _ _ sgS) 
                         (A_sg_idempotent_d _ _ _ sgT) 
; A_sg_exists_id_d   := bop_product_exists_id_decide S T rS rT bS bT 
                           (A_sg_exists_id_d _ _ _ sgS) 
                           (A_sg_exists_id_d _ _ _ sgT) 
; A_sg_exists_ann_d  :=  bop_product_exists_ann_decide S T rS rT bS bT 
                           (A_sg_exists_ann_d _ _ _ sgS) 
                           (A_sg_exists_ann_d _ _ _ sgT) 
; A_sg_left_cancel_d    := bop_product_left_cancellative_decide S T rS rT bS bT 
                            (A_eqv_nontrivial _ _ eqvS)
                            (A_eqv_reflexive _ _ eqvS)                                                                
                            (A_eqv_nontrivial _ _ eqvT)
                            (A_eqv_reflexive _ _ eqvT)
                            (A_sg_left_cancel_d _ _ _ sgS) 
                            (A_sg_left_cancel_d _ _ _ sgT) 
; A_sg_right_cancel_d   := bop_product_right_cancellative_decide S T rS rT bS bT 
                            (A_eqv_nontrivial _ _ eqvS)
                            (A_eqv_reflexive _ _ eqvS)                                                                 
                            (A_eqv_nontrivial _ _ eqvT)
                            (A_eqv_reflexive _ _ eqvT)
                            (A_sg_right_cancel_d _ _ _ sgS) 
                            (A_sg_right_cancel_d _ _ _ sgT) 
; A_sg_left_constant_d  := bop_product_left_constant_decide S T rS rT bS bT 
                            (A_eqv_nontrivial _ _ eqvS)
                            (A_eqv_nontrivial _ _ eqvT)
                            (A_sg_left_constant_d _ _ _ sgS) 
                            (A_sg_left_constant_d _ _ _ sgT) 
; A_sg_right_constant_d := bop_product_right_constant_decide S T rS rT bS bT 
                            (A_eqv_nontrivial _ _ eqvS)
                            (A_eqv_nontrivial _ _ eqvT)
                            (A_sg_right_constant_d _ _ _ sgS) 
                            (A_sg_right_constant_d _ _ _ sgT) 
; A_sg_anti_left_d      := bop_product_anti_left_decide S T rS rT bS bT 
                            (A_sg_anti_left_d _ _ _ sgS) 
                            (A_sg_anti_left_d _ _ _ sgT) 
; A_sg_anti_right_d     := bop_product_anti_right_decide S T rS rT bS bT 
                            (A_sg_anti_right_d _ _ _ sgS) 
                            (A_sg_anti_right_d _ _ _ sgT) 
|}.



Definition sg_C_proofs_product : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_C_proofs S rS bS -> 
     sg_C_proofs T rT bT -> 
        sg_C_proofs (S * T) (brel_product rS rT) (bop_product bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_C_associative   := bop_product_associative S T rS rT bS bT 
                         (A_sg_C_associative _ _ _ sgS) 
                         (A_sg_C_associative _ _ _ sgT) 
; A_sg_C_congruence    := bop_product_congruence S T rS rT bS bT 
                         (A_sg_C_congruence _ _ _ sgS) 
                         (A_sg_C_congruence _ _ _ sgT) 
; A_sg_C_commutative   := bop_product_commutative S T rS rT bS bT 
                         (A_sg_C_commutative _ _ _ sgS) 
                         (A_sg_C_commutative _ _ _ sgT) 
; A_sg_C_selective_d   := bop_product_selective_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)                                                       
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_eqv_symmetric _ _ eqvT)
                         (A_eqv_transitive _ _ eqvT)
                         (inr _ (bop_commutative_implies_not_is_left _ _ _ 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_C_commutative _ _ _ sgS))) 
                         (inr _ (bop_commutative_implies_not_is_left _ _ _ 
                                    (A_eqv_nontrivial _ _ eqvT)
                                    (A_eqv_symmetric _ _ eqvT)
                                    (A_eqv_transitive _ _ eqvT)
                                    (A_sg_C_commutative _ _ _ sgT)))
                         (inr _ (bop_commutative_implies_not_is_right _ _ _ 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_C_commutative _ _ _ sgS))) 
                         (inr _ (bop_commutative_implies_not_is_right _ _ _ 
                                    (A_eqv_nontrivial _ _ eqvT)
                                    (A_eqv_symmetric _ _ eqvT)
                                    (A_eqv_transitive _ _ eqvT)
                                    (A_sg_C_commutative _ _ _ sgT)))
; A_sg_C_idempotent_d  := bop_product_idempotent_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_sg_C_idempotent_d _ _ _ sgS) 
                         (A_sg_C_idempotent_d _ _ _ sgT) 
; A_sg_C_exists_id_d   := bop_product_exists_id_decide S T rS rT bS bT 
                           (A_sg_C_exists_id_d _ _ _ sgS) 
                           (A_sg_C_exists_id_d _ _ _ sgT) 
; A_sg_C_exists_ann_d  :=  bop_product_exists_ann_decide S T rS rT bS bT 
                           (A_sg_C_exists_ann_d _ _ _ sgS) 
                           (A_sg_C_exists_ann_d _ _ _ sgT) 
; A_sg_C_left_cancel_d    := bop_product_left_cancellative_decide S T rS rT bS bT 
                            (A_eqv_nontrivial _ _ eqvS)
                            (A_eqv_reflexive _ _ eqvS)                                                                  
                            (A_eqv_nontrivial _ _ eqvT)
                            (A_eqv_reflexive _ _ eqvT)
                            (A_sg_C_left_cancel_d _ _ _ sgS) 
                            (A_sg_C_left_cancel_d _ _ _ sgT) 
; A_sg_C_right_cancel_d   := bop_product_right_cancellative_decide S T rS rT bS bT 
                            (A_eqv_nontrivial _ _ eqvS)
                            (A_eqv_reflexive _ _ eqvS)                                                                   
                            (A_eqv_nontrivial _ _ eqvT)

                            (A_eqv_reflexive _ _ eqvT)
                            (A_sg_C_right_cancel_d _ _ _ sgS) 
                            (A_sg_C_right_cancel_d _ _ _ sgT) 
; A_sg_C_left_constant_d  := bop_product_left_constant_decide S T rS rT bS bT 
                            (A_eqv_nontrivial _ _ eqvS)
                            (A_eqv_nontrivial _ _ eqvT)
                            (A_sg_C_left_constant_d _ _ _ sgS) 
                            (A_sg_C_left_constant_d _ _ _ sgT) 
; A_sg_C_right_constant_d := bop_product_right_constant_decide S T rS rT bS bT 
                            (A_eqv_nontrivial _ _ eqvS)
                            (A_eqv_nontrivial _ _ eqvT)
                            (A_sg_C_right_constant_d _ _ _ sgS) 
                            (A_sg_C_right_constant_d _ _ _ sgT) 
; A_sg_C_anti_left_d      := bop_product_anti_left_decide S T rS rT bS bT 
                            (A_sg_C_anti_left_d _ _ _ sgS) 
                            (A_sg_C_anti_left_d _ _ _ sgT) 
; A_sg_C_anti_right_d     := bop_product_anti_right_decide S T rS rT bS bT 
                            (A_sg_C_anti_right_d _ _ _ sgS) 
                            (A_sg_C_anti_right_d _ _ _ sgT) 
|}. 

Definition sg_CI_proofs_product : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_CI_proofs S rS bS -> 
     sg_CI_proofs T rT bT -> 
        sg_CI_proofs (S * T) (brel_product rS rT) (bop_product bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_CI_associative   := bop_product_associative S T rS rT bS bT 
                         (A_sg_CI_associative _ _ _ sgS) 
                         (A_sg_CI_associative _ _ _ sgT) 
; A_sg_CI_congruence    := bop_product_congruence S T rS rT bS bT 
                         (A_sg_CI_congruence _ _ _ sgS) 
                         (A_sg_CI_congruence _ _ _ sgT) 
; A_sg_CI_commutative   := bop_product_commutative S T rS rT bS bT 
                         (A_sg_CI_commutative _ _ _ sgS) 
                         (A_sg_CI_commutative _ _ _ sgT) 
; A_sg_CI_idempotent    := bop_product_idempotent S T rS rT bS bT 
                         (A_sg_CI_idempotent _ _ _ sgS) 
                         (A_sg_CI_idempotent _ _ _ sgT) 
; A_sg_CI_selective_d   := bop_product_selective_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)                                                        
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_eqv_symmetric _ _ eqvT)
                         (A_eqv_transitive _ _ eqvT)
                         (inr _ (bop_commutative_implies_not_is_left _ _ _ 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_CI_commutative _ _ _ sgS))) 
                         (inr _ (bop_commutative_implies_not_is_left _ _ _ 
                                    (A_eqv_nontrivial _ _ eqvT)
                                    (A_eqv_symmetric _ _ eqvT)
                                    (A_eqv_transitive _ _ eqvT)
                                    (A_sg_CI_commutative _ _ _ sgT)))
                         (inr _ (bop_commutative_implies_not_is_right _ _ _ 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_CI_commutative _ _ _ sgS))) 
                         (inr _ (bop_commutative_implies_not_is_right _ _ _ 
                                    (A_eqv_nontrivial _ _ eqvT)
                                    (A_eqv_symmetric _ _ eqvT)
                                    (A_eqv_transitive _ _ eqvT)
                                    (A_sg_CI_commutative _ _ _ sgT)))
; A_sg_CI_exists_id_d   := bop_product_exists_id_decide S T rS rT bS bT 
                           (A_sg_CI_exists_id_d _ _ _ sgS) 
                           (A_sg_CI_exists_id_d _ _ _ sgT) 
; A_sg_CI_exists_ann_d  :=  bop_product_exists_ann_decide S T rS rT bS bT 
                           (A_sg_CI_exists_ann_d _ _ _ sgS) 
                           (A_sg_CI_exists_ann_d _ _ _ sgT) 
|}. 


Definition sg_CK_proofs_product : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_CK_proofs S rS bS -> 
     sg_CK_proofs T rT bT -> 
        sg_CK_proofs (S * T) (brel_product rS rT) (bop_product bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_CK_associative        := bop_product_associative S T rS rT bS bT 
                                  (A_sg_CK_associative _ _ _ sgS) 
                                  (A_sg_CK_associative _ _ _ sgT) 
; A_sg_CK_congruence         := bop_product_congruence S T rS rT bS bT 
                                  (A_sg_CK_congruence _ _ _ sgS) 
                                  (A_sg_CK_congruence _ _ _ sgT) 
; A_sg_CK_commutative        := bop_product_commutative S T rS rT bS bT 
                                  (A_sg_CK_commutative _ _ _ sgS) 
                                  (A_sg_CK_commutative _ _ _ sgT) 
; A_sg_CK_left_cancel        := bop_product_left_cancellative S T rS rT bS bT 
                                  (A_sg_CK_left_cancel _ _ _ sgS) 
                                  (A_sg_CK_left_cancel _ _ _ sgT) 
; A_sg_CK_exists_id_d        := bop_product_exists_id_decide S T rS rT bS bT 
                                  (A_sg_CK_exists_id_d _ _ _ sgS) 
                                  (A_sg_CK_exists_id_d _ _ _ sgT) 
; A_sg_CK_anti_left_d        := bop_product_anti_left_decide S T rS rT bS bT 
                                  (A_sg_CK_anti_left_d _ _ _ sgS) 
                                  (A_sg_CK_anti_left_d _ _ _ sgT) 
; A_sg_CK_anti_right_d       := bop_product_anti_right_decide S T rS rT bS bT 
                                  (A_sg_CK_anti_right_d _ _ _ sgS) 
                                  (A_sg_CK_anti_right_d _ _ _ sgT) 

|}. 



Definition A_sg_product : ∀ (S T : Type),  A_sg S -> A_sg T -> A_sg (S * T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_eq        := A_eqv_product S T 
                           (A_sg_eq S sgS) 
                           (A_sg_eq T sgT) 
   ; A_sg_bop       := bop_product 
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
   ; A_sg_proofs := sg_proofs_product S T 
                           (A_eqv_eq S (A_sg_eq S sgS)) 
                           (A_eqv_eq T (A_sg_eq T sgT))
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
                           (A_eqv_proofs S (A_sg_eq S sgS)) 
                           (A_eqv_proofs T (A_sg_eq T sgT)) 
                           (A_sg_proofs S sgS) 
                           (A_sg_proofs T sgT) 
   ; A_sg_ast       := Ast_sg_product (A_sg_ast S sgS, A_sg_ast T sgT)
   |}. 


Definition A_sg_C_product : ∀ (S T : Type),  A_sg_C S -> A_sg_C T -> A_sg_C (S * T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_C_eqv    := A_eqv_product S T 
                           (A_sg_C_eqv S sgS) 
                           (A_sg_C_eqv T sgT) 
   ; A_sg_C_bop       := bop_product 
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
   ; A_sg_C_proofs := sg_C_proofs_product S T 
                           (A_eqv_eq S (A_sg_C_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_C_eqv T sgT))
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
                           (A_eqv_proofs S (A_sg_C_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_C_eqv T sgT)) 
                           (A_sg_C_proofs S sgS) 
                           (A_sg_C_proofs T sgT) 
   ; A_sg_C_ast       := Ast_sg_C_product (A_sg_C_ast S sgS, A_sg_C_ast T sgT)
   |}. 


Definition A_sg_CI_product : ∀ (S T : Type),  A_sg_CI S -> A_sg_CI T -> A_sg_CI (S * T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CI_eqv    := A_eqv_product S T 
                           (A_sg_CI_eqv S sgS) 
                           (A_sg_CI_eqv T sgT) 
   ; A_sg_CI_bop       := bop_product 
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
   ; A_sg_CI_proofs := sg_CI_proofs_product S T 
                           (A_eqv_eq S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CI_eqv T sgT))
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CI_eqv T sgT)) 
                           (A_sg_CI_proofs S sgS) 
                           (A_sg_CI_proofs T sgT) 
   ; A_sg_CI_ast       := Ast_sg_CI_product (A_sg_CI_ast S sgS, A_sg_CI_ast T sgT)
   |}. 


Definition A_sg_CK_product : ∀ (S T : Type),  A_sg_CK S -> A_sg_CK T -> A_sg_CK (S * T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CK_eqv    := A_eqv_product S T 
                           (A_sg_CK_eqv S sgS) 
                           (A_sg_CK_eqv T sgT) 
   ; A_sg_CK_bop       := bop_product 
                           (A_sg_CK_bop S sgS) 
                           (A_sg_CK_bop T sgT) 
   ; A_sg_CK_proofs := sg_CK_proofs_product S T 
                           (A_eqv_eq S (A_sg_CK_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CK_eqv T sgT))
                           (A_sg_CK_bop S sgS) 
                           (A_sg_CK_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CK_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CK_eqv T sgT)) 
                           (A_sg_CK_proofs S sgS) 
                           (A_sg_CK_proofs T sgT) 
   ; A_sg_CK_ast       := Ast_sg_CK_product (A_sg_CK_ast S sgS, A_sg_CK_ast T sgT)
   |}. 


