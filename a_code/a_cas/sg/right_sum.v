Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.bop.right_sum.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cas.eqv.sum.
Require Import CAS.theory.facts. 




Definition sg_C_proofs_right_sum : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_C_proofs S rS bS -> 
     sg_C_proofs T rT bT -> 
        sg_C_proofs (S + T) (brel_sum rS rT) (bop_right_sum bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT,
let assS := A_sg_C_associative _ _ _ sgS in
let assT := A_sg_C_associative _ _ _ sgT in     
let refT := A_eqv_reflexive _ _ eqvT in
let conS := A_sg_C_congruence _ _ _ sgS in
let conT := A_sg_C_congruence _ _ _ sgT in
let comS := A_sg_C_commutative _ _ _ sgS in
let comT := A_sg_C_commutative _ _ _ sgT in
let selS := A_sg_C_selective_d _ _ _ sgS in
let selT := A_sg_C_selective_d _ _ _ sgT in
let idmS := A_sg_C_idempotent_d _ _ _ sgS in
let idmT := A_sg_C_idempotent_d _ _ _ sgT in
let idS  := A_sg_C_exists_id_d _ _ _ sgS in
let annT := A_sg_C_exists_ann_d _ _ _ sgT in 
let ntS  := A_eqv_nontrivial _ _ eqvS in
let ntT  := A_eqv_nontrivial _ _ eqvT in
let wS   := brel_get_nontrivial_witness _ _ ntS in  
let wT   := brel_get_nontrivial_witness _ _ ntT in  
{|
  A_sg_C_associative   := bop_right_sum_associative S T rS rT bS bT refT assS assT 
; A_sg_C_congruence    := bop_right_sum_congruence S T rS rT bS bT conS conT
; A_sg_C_commutative   := bop_right_sum_commutative S T rS rT bS bT refT comS comT 
; A_sg_C_selective_d   := bop_right_sum_selective_decide S T rS rT bS bT refT selS selT
; A_sg_C_idempotent_d  := bop_right_sum_idempotent_decide S T rS rT bS bT idmS idmT 
; A_sg_C_exists_id_d   := bop_right_sum_exists_id_decide S T rS rT bS bT ntS refT idS  
; A_sg_C_exists_ann_d  := bop_right_sum_exists_ann_decide S T rS rT bS bT ntT refT annT 
; A_sg_C_left_cancel_d    := inr _ (bop_right_sum_not_left_cancellative S T rS rT bS bT ntS refT wT) 
; A_sg_C_right_cancel_d   := inr _ (bop_right_sum_not_right_cancellative S T rS rT bS bT ntS refT wT) 
; A_sg_C_left_constant_d  := inr _ (bop_right_sum_not_left_constant S T rS rT bS bT ntT wS)
; A_sg_C_right_constant_d := inr _ (bop_right_sum_not_right_constant S T rS rT bS bT ntT wS)
; A_sg_C_anti_left_d      := inr _ (bop_right_sum_not_anti_left S T rS rT bS bT refT wS wT)
; A_sg_C_anti_right_d     := inr _ (bop_right_sum_not_anti_right S T rS rT bS bT refT wS wT)
|}. 


Definition sg_proofs_right_sum : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_proofs S rS bS -> 
     sg_proofs T rT bT -> 
        sg_proofs (S + T) (brel_sum rS rT) (bop_right_sum bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_associative   := bop_right_sum_associative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_associative _ _ _ sgS) 
                         (A_sg_associative _ _ _ sgT) 
; A_sg_congruence    := bop_right_sum_congruence S T rS rT bS bT 
                         (A_sg_congruence _ _ _ sgS) 
                         (A_sg_congruence _ _ _ sgT) 
; A_sg_commutative_d := bop_right_sum_commutative_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_commutative_d _ _ _ sgS) 
                         (A_sg_commutative_d _ _ _ sgT) 
; A_sg_selective_d   := bop_right_sum_selective_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_selective_d _ _ _ sgS) 
                         (A_sg_selective_d _ _ _ sgT) 
; A_sg_is_left_d     := inr _ (bop_right_sum_not_is_left S T rS rT bS bT 
                         (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                         (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT)))
; A_sg_is_right_d    := inr _ (bop_right_sum_not_is_right S T rS rT bS bT 
                         (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                         (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT)))
; A_sg_idempotent_d  := bop_right_sum_idempotent_decide S T rS rT bS bT 
                         (A_sg_idempotent_d _ _ _ sgS) 
                         (A_sg_idempotent_d _ _ _ sgT) 
; A_sg_exists_id_d   := bop_right_sum_exists_id_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_exists_id_d _ _ _ sgS) 
; A_sg_exists_ann_d  := bop_right_sum_exists_ann_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_exists_ann_d _ _ _ sgT) 
; A_sg_left_cancel_d    := inr _ (bop_right_sum_not_left_cancellative S T rS rT bS bT
                                    (A_eqv_nontrivial _ _ eqvS)                                                                      
                                    (A_eqv_reflexive _ _ eqvT)                                                                      
                                    (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                           ) 
; A_sg_right_cancel_d   := inr _ (bop_right_sum_not_right_cancellative S T rS rT bS bT
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_reflexive _ _ eqvT)
                                    (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                           ) 
; A_sg_left_constant_d  := inr _ (bop_right_sum_not_left_constant S T rS rT bS bT
                                    (A_eqv_nontrivial _ _ eqvT)                                                                  
                                    (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                           ) 
; A_sg_right_constant_d := inr _ (bop_right_sum_not_right_constant S T rS rT bS bT
                                    (A_eqv_nontrivial _ _ eqvT)
                                    (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                           ) 
; A_sg_anti_left_d      := inr _ (bop_right_sum_not_anti_left S T rS rT bS bT
                                    (A_eqv_reflexive _ _ eqvT)                                                               
                                    (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                           ) 
; A_sg_anti_right_d     := inr _ (bop_right_sum_not_anti_right S T rS rT bS bT
                                    (A_eqv_reflexive _ _ eqvT)                                                                  
                                    (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                           ) 
|}. 


Definition sg_CI_proofs_right_sum : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_CI_proofs S rS bS -> 
     sg_CI_proofs T rT bT -> 
        sg_CI_proofs (S + T) (brel_sum rS rT) (bop_right_sum bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_CI_associative   := bop_right_sum_associative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CI_associative _ _ _ sgS) 
                         (A_sg_CI_associative _ _ _ sgT) 
; A_sg_CI_congruence    := bop_right_sum_congruence S T rS rT bS bT 
                         (A_sg_CI_congruence _ _ _ sgS) 
                         (A_sg_CI_congruence _ _ _ sgT) 
; A_sg_CI_commutative   := bop_right_sum_commutative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CI_commutative _ _ _ sgS) 
                         (A_sg_CI_commutative _ _ _ sgT) 
; A_sg_CI_selective_d   := bop_right_sum_selective_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CI_selective_d _ _ _ sgS) 
                         (A_sg_CI_selective_d _ _ _ sgT) 
; A_sg_CI_idempotent     := bop_right_sum_idempotent S T rS rT bS bT 
                         (A_sg_CI_idempotent _ _ _ sgS) 
                         (A_sg_CI_idempotent _ _ _ sgT) 
; A_sg_CI_exists_id_d   := bop_right_sum_exists_id_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CI_exists_id_d _ _ _ sgS) 
; A_sg_CI_exists_ann_d  := bop_right_sum_exists_ann_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CI_exists_ann_d _ _ _ sgT) 
|}. 



Definition sg_CS_proofs_right_sum : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_CS_proofs S rS bS -> 
     sg_CS_proofs T rT bT -> 
        sg_CS_proofs (S + T) (brel_sum rS rT) (bop_right_sum bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_CS_associative   := bop_right_sum_associative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_associative _ _ _ sgS) 
                         (A_sg_CS_associative _ _ _ sgT) 
; A_sg_CS_congruence    := bop_right_sum_congruence S T rS rT bS bT 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_CS_congruence _ _ _ sgT) 
; A_sg_CS_commutative   := bop_right_sum_commutative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_commutative _ _ _ sgS) 
                         (A_sg_CS_commutative _ _ _ sgT) 
; A_sg_CS_selective   := bop_right_sum_selective S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sgT) 
; A_sg_CS_exists_id_d   := bop_right_sum_exists_id_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_exists_id_d _ _ _ sgS) 
; A_sg_CS_exists_ann_d  := bop_right_sum_exists_ann_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_exists_ann_d _ _ _ sgT) 
|}. 


(* CK sums? Sums are never cancellative! *) 


Definition A_sg_right_sum : ∀ (S T : Type),  A_sg S -> A_sg T -> A_sg (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_eq        := A_eqv_sum S T 
                           (A_sg_eq S sgS) 
                           (A_sg_eq T sgT) 
   ; A_sg_bop       := bop_right_sum 
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
   ; A_sg_proofs := sg_proofs_right_sum S T 
                           (A_eqv_eq S (A_sg_eq S sgS)) 
                           (A_eqv_eq T (A_sg_eq T sgT))
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
                           (A_eqv_proofs S (A_sg_eq S sgS)) 
                           (A_eqv_proofs T (A_sg_eq T sgT)) 
                           (A_sg_proofs S sgS) 
                           (A_sg_proofs T sgT) 
   ; A_sg_ast       := Ast_sg_right_sum (A_sg_ast S sgS, A_sg_ast T sgT)
   |}. 




Definition A_sg_C_right_sum : ∀ (S T : Type),  A_sg_C S -> A_sg_C T -> A_sg_C (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_C_eqv       := A_eqv_sum S T 
                           (A_sg_C_eqv S sgS) 
                           (A_sg_C_eqv T sgT) 
   ; A_sg_C_bop       := bop_right_sum 
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
   ; A_sg_C_proofs := sg_C_proofs_right_sum S T 
                           (A_eqv_eq S (A_sg_C_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_C_eqv T sgT))
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
                           (A_eqv_proofs S (A_sg_C_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_C_eqv T sgT)) 
                           (A_sg_C_proofs S sgS) 
                           (A_sg_C_proofs T sgT) 
   ; A_sg_C_ast       := Ast_sg_C_right_sum (A_sg_C_ast S sgS, A_sg_C_ast T sgT)
   |}. 


Definition A_sg_CI_right_sum : ∀ (S T : Type),  A_sg_CI S -> A_sg_CI T -> A_sg_CI (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CI_eqv       := A_eqv_sum S T 
                           (A_sg_CI_eqv S sgS) 
                           (A_sg_CI_eqv T sgT) 
   ; A_sg_CI_bop       := bop_right_sum 
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
   ; A_sg_CI_proofs := sg_CI_proofs_right_sum S T 
                           (A_eqv_eq S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CI_eqv T sgT))
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CI_eqv T sgT)) 
                           (A_sg_CI_proofs S sgS) 
                           (A_sg_CI_proofs T sgT) 
   ; A_sg_CI_ast       := Ast_sg_CI_right_sum (A_sg_CI_ast S sgS, A_sg_CI_ast T sgT)
   |}. 



Definition A_sg_CS_right_sum : ∀ (S T : Type),  A_sg_CS S -> A_sg_CS T -> A_sg_CS (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CS_eqv       := A_eqv_sum S T 
                           (A_sg_CS_eqv S sgS) 
                           (A_sg_CS_eqv T sgT) 
   ; A_sg_CS_bop       := bop_right_sum 
                           (A_sg_CS_bop S sgS) 
                           (A_sg_CS_bop T sgT) 
   ; A_sg_CS_proofs := sg_CS_proofs_right_sum S T 
                           (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CS_eqv T sgT))
                           (A_sg_CS_bop S sgS) 
                           (A_sg_CS_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CS_eqv T sgT)) 
                           (A_sg_CS_proofs S sgS) 
                           (A_sg_CS_proofs T sgT) 
   ; A_sg_CS_ast       := Ast_sg_CS_right_sum (A_sg_CS_ast S sgS, A_sg_CS_ast T sgT)
   |}. 
gtg
