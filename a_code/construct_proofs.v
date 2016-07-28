Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.facts. 

Require Import CAS.theory.brel.eq_bool.
Require Import CAS.theory.brel.to_bool.  
Require Import CAS.theory.brel.eq_nat. 
Require Import CAS.theory.brel.to_nat. 
Require Import CAS.theory.brel.eq_list. 
Require Import CAS.theory.brel.product. 
Require Import CAS.theory.brel.llte_llt. 
Require Import CAS.theory.brel.dual. 
Require Import CAS.theory.brel.llte_llt. 
Require Import CAS.theory.brel.sum. 
Require Import CAS.theory.brel.add_constant. 
Require Import CAS.theory.brel.and_sym.
Require Import CAS.theory.brel.reduce. 


Require Import CAS.theory.bop.and. 
Require Import CAS.theory.bop.or. 
Require Import CAS.theory.bop.max. 
Require Import CAS.theory.bop.min. 
Require Import CAS.theory.bop.plus. 
Require Import CAS.theory.bop.times. 
Require Import CAS.theory.bop.concat. 
Require Import CAS.theory.bop.left. 
Require Import CAS.theory.bop.right. 
Require Import CAS.theory.bop.product. 
Require Import CAS.theory.bop.left_sum. 
Require Import CAS.theory.bop.right_sum. 
Require Import CAS.theory.bop.add_id. 
Require Import CAS.theory.bop.add_ann. 
Require Import CAS.theory.bop.then_unary. 
Require Import CAS.theory.bop.llex. 

Require Import CAS.theory.bops.and_or.
Require Import CAS.theory.bops.or_and.
Require Import CAS.theory.bops.min_max.
Require Import CAS.theory.bops.max_min.
Require Import CAS.theory.bops.min_plus.
Require Import CAS.theory.bops.max_plus.
Require Import CAS.theory.bops.product_product.
Require Import CAS.theory.bops.llex_product.
Require Import CAS.theory.bops.add_ann_add_id.
Require Import CAS.theory.bops.add_id_add_ann.


Require Import CAS.theory.brel.set. 
Require Import CAS.theory.brel.in_set. 
Require Import CAS.theory.bop.union. 
Require Import CAS.theory.bop.intersect. 
(*Require Import CAS.theory.bop.minset_union. *) 
Require Import CAS.theory.bops.union_intersect.
Require Import CAS.theory.bops.intersect_union.



Require Import CAS.theory.properties.        (* ~~ code.certificates *) 
Require Import CAS.a_code.proof_records.     (* ~~ code.cert_records *) 
Require Import CAS.a_code.decide.            (* ~~ code.check        *) 
Require Import CAS.a_code.a_cas_records. 


(* eqv *) 


Definition eqv_proofs_eq_bool : eqv_proofs bool brel_eq_bool 
:= {| 
     A_eqv_nontrivial  := brel_eq_bool_nontrivial
   ; A_eqv_congruence  := brel_eq_bool_congruence 
   ; A_eqv_reflexive   := brel_eq_bool_reflexive 
   ; A_eqv_transitive  := brel_eq_bool_transitive 
   ; A_eqv_symmetric   := brel_eq_bool_symmetric
   |}. 

Open Scope nat. 

Definition eqv_proofs_eq_nat : eqv_proofs nat brel_eq_nat 
:= {| 
     A_eqv_nontrivial  := brel_eq_nat_nontrivial
   ; A_eqv_congruence  := brel_eq_nat_congruence 
   ; A_eqv_reflexive   := brel_eq_nat_reflexive 
   ; A_eqv_transitive  := brel_eq_nat_transitive 
   ; A_eqv_symmetric   := brel_eq_nat_symmetric
   |}. 


Definition eqv_proofs_add_constant : ∀ (S : Type) (r : brel S) (c : cas_constant), 
              (eqv_proofs S r) → eqv_proofs (with_constant S) (brel_add_constant S r c)
:= λ S r c eqv, 
   {| 
     A_eqv_nontrivial  := brel_add_constant_nontrivial S r c (A_eqv_nontrivial S r eqv) 
   ; A_eqv_congruence  := brel_add_constant_congruence S r c (A_eqv_congruence S r eqv) 
   ; A_eqv_reflexive   := brel_add_constant_reflexive S r c (A_eqv_reflexive S r eqv) 
   ; A_eqv_transitive  := brel_add_constant_transitive S r c (A_eqv_transitive S r eqv) 
   ; A_eqv_symmetric   := brel_add_constant_symmetric S r c (A_eqv_symmetric S r eqv) 
   |}. 



Open Scope list_scope. 


Definition eqv_proofs_brel_list : ∀ (S : Type) (r : brel S), 
              (eqv_proofs S r) → eqv_proofs (list S) (brel_list S r)
:= λ S r eqv, 
   {| 
     A_eqv_nontrivial := brel_list_nontrivial S r 
                                  (A_eqv_symmetric S r eqv) 
                                  (A_eqv_nontrivial S r eqv)
   ; A_eqv_congruence  := brel_list_congruence S r 
                                  (A_eqv_symmetric S r eqv) 
                                  (A_eqv_transitive S r eqv) 
                                  (A_eqv_congruence S r eqv) 
   ; A_eqv_reflexive   := brel_list_reflexive S r (A_eqv_reflexive S r eqv) 
   ; A_eqv_transitive  := brel_list_transitive S r (A_eqv_transitive S r eqv) 
   ; A_eqv_symmetric   := brel_list_symmetric S r (A_eqv_symmetric S r eqv) 
   |}. 



Definition eqv_proofs_brel_set : ∀ (S : Type) (r : brel S), 
              (eqv_proofs S r) → eqv_proofs (finite_set S) (brel_set S r)
:= λ S r eqv, 
   {| 
     A_eqv_nontrivial := brel_set_nontrivial S r 
                                  (A_eqv_symmetric S r eqv) 
                                  (A_eqv_nontrivial S r eqv)
   ; A_eqv_congruence  := brel_set_congruence S r 
                                  (A_eqv_reflexive S r eqv) 
                                  (A_eqv_symmetric S r eqv) 
                                  (A_eqv_transitive S r eqv) 
   ; A_eqv_reflexive   := brel_set_reflexive S r 
                                  (A_eqv_reflexive S r eqv) 
                                  (A_eqv_symmetric S r eqv) 
                                  (A_eqv_transitive S r eqv) 
   ; A_eqv_transitive  := brel_set_transitive S r 
                                  (A_eqv_reflexive S r eqv) 
                                  (A_eqv_symmetric S r eqv) 
                                  (A_eqv_transitive S r eqv) 
   ; A_eqv_symmetric   := brel_set_symmetric S r (A_eqv_symmetric S r eqv) 
   |}. 


Definition eqv_proofs_product : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T), 
       eqv_proofs S rS -> eqv_proofs T rT -> eqv_proofs (S * T) (brel_product S T rS rT) 
:= λ S T rS rT eqvS eqvT, 
{|
  A_eqv_nontrivial := brel_product_nontrivial S T rS rT 
                        (A_eqv_nontrivial _ _ eqvS)
                        (A_eqv_nontrivial _ _ eqvT)
; A_eqv_congruence  := brel_product_congruence S T rS rT rS rT 
                        (A_eqv_congruence S rS eqvS)
                        (A_eqv_congruence T rT eqvT)
; A_eqv_reflexive   := brel_product_reflexive S T rS rT 
                        (A_eqv_reflexive S rS eqvS) 
                        (A_eqv_reflexive T rT eqvT) 
; A_eqv_transitive  := brel_product_transitive S T rS rT  
                        (A_eqv_transitive S rS eqvS) 
                        (A_eqv_transitive T rT eqvT) 
; A_eqv_symmetric   := brel_product_symmetric S T rS rT  
                        (A_eqv_symmetric S rS eqvS) 
                        (A_eqv_symmetric T rT eqvT) 
|}.


Definition eqv_proofs_sum : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T), 
       eqv_proofs S rS -> eqv_proofs T rT -> eqv_proofs (S + T) (brel_sum S T rS rT) 
:= λ S T rS rT eqvS eqvT, 
{|
  A_eqv_nontrivial := brel_sum_nontrivial S T rS rT 
                        (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                        (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
; A_eqv_congruence  := brel_sum_congruence S T rS rT 
                        (A_eqv_congruence S rS eqvS)
                        (A_eqv_congruence T rT eqvT)
; A_eqv_reflexive   := brel_sum_reflexive S T rS rT 
                        (A_eqv_reflexive S rS eqvS) 
                        (A_eqv_reflexive T rT eqvT) 
; A_eqv_transitive  := brel_sum_transitive S T rS rT  
                        (A_eqv_transitive S rS eqvS) 
                        (A_eqv_transitive T rT eqvT) 
; A_eqv_symmetric   := brel_sum_symmetric S T rS rT  
                        (A_eqv_symmetric S rS eqvS) 
                        (A_eqv_symmetric T rT eqvT) 
|}.



(* orders *) 

Definition to_proofs_bool : to_proofs bool brel_eq_bool brel_to_bool
:= {|
  A_to_congruence  := brel_to_bool_congruence
; A_to_reflexive   := brel_to_bool_reflexive
; A_to_transitive  := brel_to_bool_transitive
; A_to_antisymmetric   := brel_to_bool_antisymmetric
; A_to_total       := brel_to_bool_total
|}.

Definition to_proofs_nat : to_proofs nat brel_eq_nat brel_to_nat 
:= {|
  A_to_congruence  := brel_to_nat_congruence
; A_to_reflexive   := brel_to_nat_reflexive
; A_to_transitive  := brel_to_nat_transitive
; A_to_antisymmetric   := brel_to_nat_antisymmetric
; A_to_total       := brel_to_nat_total
|}.

Definition po_proofs_dual : ∀ (S : Type) (eq po : brel S), 
               po_proofs S eq po -> po_proofs S eq (brel_dual S po)
:= λ S eq po tpS, 
{|
  A_po_congruence  := brel_dual_congruence S eq po (A_po_congruence _ _ _ tpS)
; A_po_reflexive   := brel_dual_reflexive S po (A_po_reflexive _ _ _ tpS)
; A_po_transitive  := brel_dual_transitive S po (A_po_transitive _ _ _ tpS)
; A_po_antisymmetric := brel_dual_antisymmetric S eq po (A_po_antisymmetric _ _ _ tpS)
; A_po_total_d       := brel_dual_total_decide S po (A_po_total_d _ _ _ tpS)
|}.

Definition to_proofs_dual : ∀ (S : Type) (eq po : brel S), 
               to_proofs S eq po -> to_proofs S eq (brel_dual S po)
:= λ S eq po tpS, 
{|
  A_to_congruence  := brel_dual_congruence S eq po (A_to_congruence _ _ _ tpS)
; A_to_reflexive   := brel_dual_reflexive S po (A_to_reflexive _ _ _ tpS)
; A_to_transitive  := brel_dual_transitive S po (A_to_transitive _ _ _ tpS)
; A_to_antisymmetric   := brel_dual_antisymmetric S eq po (A_to_antisymmetric _ _ _ tpS)
; A_to_total       := brel_dual_total S po (A_to_total _ _ _ tpS)
|}.




Definition po_proofs_llte : ∀ (S : Type) (r : brel S) (b : binary_op S), 
               eqv_proofs S r -> 
               sg_CI_proofs S r b -> po_proofs S r (brel_llte S r b)
:= λ S r b eqv sgp, 
{|
  A_po_congruence  := brel_llte_congruence S r r b 
                         (A_eqv_congruence _ _ eqv)
                         (A_sg_CI_congruence _ _ _ sgp)
; A_po_reflexive   := brel_llte_reflexive S r b 
                         (A_eqv_symmetric _ _ eqv)
                         (A_sg_CI_idempotent _ _ _ sgp)
                         (A_eqv_reflexive _ _ eqv)
; A_po_transitive  := brel_llte_transitive S r b 
                         (A_eqv_reflexive _ _ eqv)
                         (A_eqv_symmetric _ _ eqv)
                         (A_sg_CI_associative _ _ _ sgp) 
                         (A_sg_CI_congruence _ _ _ sgp)
                         (A_eqv_transitive _ _ eqv)
; A_po_antisymmetric := brel_llte_antisymmetric S r b 
                         (A_eqv_symmetric _ _ eqv)
                         (A_eqv_transitive _ _ eqv)
                         (A_sg_CI_commutative _ _ _ sgp) 
; A_po_total_d      := brel_llte_total_decide S r b 
                         (A_eqv_symmetric _ _ eqv)
                         (A_eqv_transitive _ _ eqv)
                         (A_sg_CI_commutative _ _ _ sgp) 
                         (A_sg_CI_selective_d _ _ _ sgp)
|}.

Definition to_proofs_llte : ∀ (S : Type) (r : brel S) (b : binary_op S), 
               eqv_proofs S r -> 
               sg_CS_proofs S r b -> to_proofs S r (brel_llte S r b)
:= λ S r b eqv sgp, 
{|
  A_to_congruence  := brel_llte_congruence S r r b 
                         (A_eqv_congruence _ _ eqv)
                         (A_sg_CS_congruence _ _ _ sgp)
; A_to_reflexive   := brel_llte_reflexive S r b 
                         (A_eqv_symmetric _ _ eqv)
                         (bop_selective_implies_idempotent  _ _ _ 
                            (A_sg_CS_selective _ _ _ sgp))
                         (A_eqv_reflexive _ _ eqv)
; A_to_transitive  := brel_llte_transitive S r b 
                         (A_eqv_reflexive _ _ eqv)
                         (A_eqv_symmetric _ _ eqv)
                         (A_sg_CS_associative _ _ _ sgp) 
                         (A_sg_CS_congruence _ _ _ sgp)
                         (A_eqv_transitive _ _ eqv)
; A_to_antisymmetric := brel_llte_antisymmetric S r b 
                         (A_eqv_symmetric _ _ eqv)
                         (A_eqv_transitive _ _ eqv)
                         (A_sg_CS_commutative _ _ _ sgp) 
; A_to_total         := brel_llte_total S r b 
                         (A_eqv_symmetric _ _ eqv)
                         (A_eqv_transitive _ _ eqv)
                         (A_sg_CS_commutative _ _ _ sgp) 
                         (A_sg_CS_selective _ _ _ sgp)
|}.



(* semigroups *) 

(* basics *) 


Definition sg_proofs_and : sg_proofs bool brel_eq_bool bop_and := 
{| 
  A_sg_associative   := bop_and_associative
; A_sg_congruence    := bop_and_congruence
; A_sg_commutative_d := inl _ bop_and_commutative
; A_sg_selective_d   := inl _ bop_and_selective
; A_sg_idempotent_d  := inl _ (bop_selective_implies_idempotent bool brel_eq_bool bop_and  
                                 bop_and_selective)
; A_sg_exists_id_d   := inl _ bop_and_exists_id 
; A_sg_exists_ann_d  := inl _ bop_and_exists_ann 

; A_sg_is_left_d     := inr _ (bop_commutative_implies_not_is_left bool brel_eq_bool bop_and  
                                     brel_eq_bool_nontrivial
                                     brel_eq_bool_symmetric
                                     brel_eq_bool_transitive 
                                     bop_and_commutative)
; A_sg_is_right_d   := inr _ (bop_commutative_implies_not_is_right bool brel_eq_bool bop_and  
                                     brel_eq_bool_nontrivial
                                     brel_eq_bool_symmetric
                                     brel_eq_bool_transitive 
                                     bop_and_commutative)

; A_sg_left_cancel_d := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative bool brel_eq_bool bop_and  
                                       brel_eq_bool_congruence 
                                       brel_eq_bool_nontrivial
                                       brel_eq_bool_reflexive 
                                       brel_eq_bool_symmetric
                                       brel_eq_bool_transitive 
                                       bop_and_associative
                                       bop_and_congruence 
                                       (bop_selective_implies_idempotent bool brel_eq_bool bop_and  
                                            bop_and_selective)
                                       bop_and_commutative
                                       (inl _ bop_and_selective)
                                   )
; A_sg_right_cancel_d := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_right_cancellative bool brel_eq_bool bop_and  
                                       brel_eq_bool_congruence 
                                       brel_eq_bool_nontrivial
                                       brel_eq_bool_reflexive 
                                       brel_eq_bool_symmetric
                                       brel_eq_bool_transitive 
                                       bop_and_associative
                                       bop_and_congruence 
                                       (bop_selective_implies_idempotent bool brel_eq_bool bop_and  
                                            bop_and_selective)
                                       bop_and_commutative
                                       (inl _ bop_and_selective)
                                   )
; A_sg_left_constant_d := inr _ (bop_idempotent_and_commutative_imply_not_left_constant bool brel_eq_bool bop_and  
                                       brel_eq_bool_nontrivial
                                       brel_eq_bool_congruence 
                                       brel_eq_bool_reflexive 
                                       brel_eq_bool_transitive
                                       (bop_selective_implies_idempotent bool brel_eq_bool bop_and  
                                            bop_and_selective) 
                                       bop_and_commutative
                                   ) 
; A_sg_right_constant_d := inr _ (bop_idempotent_and_commutative_imply_not_right_constant bool brel_eq_bool bop_and  
                                       brel_eq_bool_nontrivial
                                       brel_eq_bool_congruence 
                                       brel_eq_bool_reflexive 
                                       brel_eq_bool_symmetric
                                       brel_eq_bool_transitive
                                       (bop_selective_implies_idempotent bool brel_eq_bool bop_and  
                                            bop_and_selective) 
                                       bop_and_commutative
                                   ) 
; A_sg_anti_left_d      := inr _ (bop_idempotent_implies_not_anti_left bool brel_eq_bool bop_and  
                                       (brel_nontrivial_witness bool brel_eq_bool brel_eq_bool_nontrivial) 
                                       brel_eq_bool_symmetric
                                       (bop_selective_implies_idempotent bool brel_eq_bool bop_and  
                                            bop_and_selective) 
                                   )
; A_sg_anti_right_d     := inr _ (bop_idempotent_implies_not_anti_right bool brel_eq_bool bop_and  
                                       (brel_nontrivial_witness bool brel_eq_bool brel_eq_bool_nontrivial) 
                                       brel_eq_bool_symmetric
                                       (bop_selective_implies_idempotent bool brel_eq_bool bop_and  
                                            bop_and_selective) 
                                   )

|}. 



Definition sg_CS_proofs_and : sg_CS_proofs bool brel_eq_bool bop_and := 
{| 
  A_sg_CS_associative  := bop_and_associative
; A_sg_CS_congruence   := bop_and_congruence
; A_sg_CS_commutative  := bop_and_commutative
; A_sg_CS_selective    := bop_and_selective
; A_sg_CS_exists_id_d  := inl _ bop_and_exists_id 
; A_sg_CS_exists_ann_d := inl _ bop_and_exists_ann 
|}. 



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

Definition sg_CS_proofs_or : sg_CS_proofs bool brel_eq_bool bop_or := 
{| 
  A_sg_CS_associative  := bop_or_associative
; A_sg_CS_congruence   := bop_or_congruence
; A_sg_CS_commutative  := bop_or_commutative
; A_sg_CS_selective    := bop_or_selective
; A_sg_CS_exists_id_d  := inl _ bop_or_exists_id 
; A_sg_CS_exists_ann_d := inl _ bop_or_exists_ann
|}. 



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




Definition sg_CS_proofs_min : sg_CS_proofs nat brel_eq_nat bop_min := 
{| 
  A_sg_CS_associative  := bop_min_associative
; A_sg_CS_congruence   := bop_min_congruence
; A_sg_CS_commutative  := bop_min_commutative
; A_sg_CS_selective    := bop_min_selective
; A_sg_CS_exists_id_d  := inr _ bop_min_not_exists_id
; A_sg_CS_exists_ann_d := inl _ bop_min_exists_ann
|}. 


Definition sg_proofs_max : sg_proofs nat brel_eq_nat bop_max := 
{| 
  A_sg_associative   := bop_max_associative
; A_sg_congruence    := bop_max_congruence
; A_sg_commutative_d := inl _ bop_max_commutative
; A_sg_selective_d   := inl _ bop_max_selective
; A_sg_idempotent_d  := inl _ (bop_selective_implies_idempotent nat brel_eq_nat bop_max  
                                 bop_max_selective)
; A_sg_exists_id_d  :=  inl _ bop_max_exists_id
; A_sg_exists_ann_d  := inr _ bop_max_not_exists_ann

; A_sg_is_left_d     := inr _ (bop_commutative_implies_not_is_left nat brel_eq_nat bop_max  
                                     brel_eq_nat_nontrivial
                                     brel_eq_nat_symmetric
                                     brel_eq_nat_transitive 
                                     bop_max_commutative)
; A_sg_is_right_d   := inr _ (bop_commutative_implies_not_is_right nat brel_eq_nat bop_max  
                                     brel_eq_nat_nontrivial
                                     brel_eq_nat_symmetric
                                     brel_eq_nat_transitive 
                                     bop_max_commutative)

; A_sg_left_cancel_d := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative nat brel_eq_nat bop_max  
                                       brel_eq_nat_congruence 
                                       brel_eq_nat_nontrivial
                                       brel_eq_nat_reflexive 
                                       brel_eq_nat_symmetric
                                       brel_eq_nat_transitive 
                                       bop_max_associative
                                       bop_max_congruence 
                                       (bop_selective_implies_idempotent nat brel_eq_nat bop_max  
                                            bop_max_selective)
                                       bop_max_commutative
                                       (inl _ bop_max_selective)
                                   )
; A_sg_right_cancel_d := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_right_cancellative nat brel_eq_nat bop_max  
                                       brel_eq_nat_congruence 
                                       brel_eq_nat_nontrivial
                                       brel_eq_nat_reflexive 
                                       brel_eq_nat_symmetric
                                       brel_eq_nat_transitive 
                                       bop_max_associative
                                       bop_max_congruence 
                                       (bop_selective_implies_idempotent nat brel_eq_nat bop_max  
                                            bop_max_selective)
                                       bop_max_commutative
                                       (inl _ bop_max_selective)
                                   )
; A_sg_left_constant_d := inr _ (bop_idempotent_and_commutative_imply_not_left_constant nat brel_eq_nat bop_max  
                                       brel_eq_nat_nontrivial
                                       brel_eq_nat_congruence 
                                       brel_eq_nat_reflexive 
                                       brel_eq_nat_transitive
                                       (bop_selective_implies_idempotent nat brel_eq_nat bop_max  
                                            bop_max_selective) 
                                       bop_max_commutative
                                   ) 
; A_sg_right_constant_d := inr _ (bop_idempotent_and_commutative_imply_not_right_constant nat brel_eq_nat bop_max  
                                       brel_eq_nat_nontrivial
                                       brel_eq_nat_congruence 
                                       brel_eq_nat_reflexive 
                                       brel_eq_nat_symmetric
                                       brel_eq_nat_transitive
                                       (bop_selective_implies_idempotent nat brel_eq_nat bop_max  
                                            bop_max_selective) 
                                       bop_max_commutative
                                   ) 
; A_sg_anti_left_d      := inr _ (bop_idempotent_implies_not_anti_left nat brel_eq_nat bop_max  
                                       (brel_nontrivial_witness nat brel_eq_nat brel_eq_nat_nontrivial) 
                                       brel_eq_nat_symmetric
                                       (bop_selective_implies_idempotent nat brel_eq_nat bop_max  
                                            bop_max_selective) 
                                   )
; A_sg_anti_right_d     := inr _ (bop_idempotent_implies_not_anti_right nat brel_eq_nat bop_max  
                                       (brel_nontrivial_witness nat brel_eq_nat brel_eq_nat_nontrivial) 
                                       brel_eq_nat_symmetric
                                       (bop_selective_implies_idempotent nat brel_eq_nat bop_max  
                                            bop_max_selective) 
                                   )

|}. 


Definition sg_CS_proofs_max : sg_CS_proofs nat brel_eq_nat bop_max := 
{| 
  A_sg_CS_associative  := bop_max_associative
; A_sg_CS_congruence   := bop_max_congruence
; A_sg_CS_commutative  := bop_max_commutative
; A_sg_CS_selective    := bop_max_selective
; A_sg_CS_exists_id_d  := inl _ bop_max_exists_id
; A_sg_CS_exists_ann_d := inr _ bop_max_not_exists_ann
|}. 


Definition sg_proofs_times : sg_proofs nat brel_eq_nat bop_times := 
{| 
  A_sg_associative      := bop_times_associative
; A_sg_congruence       := bop_times_congruence
; A_sg_commutative_d    := inl _ bop_times_commutative
; A_sg_selective_d      := inr _ bop_times_not_selective
; A_sg_idempotent_d     := inr _ bop_times_not_idempotent 
; A_sg_exists_id_d      := inl _ bop_times_exists_id
; A_sg_exists_ann_d     := inl _ bop_times_exists_ann

; A_sg_is_left_d     := inr _ (bop_commutative_implies_not_is_left nat brel_eq_nat bop_times
                                     brel_eq_nat_nontrivial
                                     brel_eq_nat_symmetric
                                     brel_eq_nat_transitive 
                                     bop_times_commutative)
; A_sg_is_right_d   := inr _ (bop_commutative_implies_not_is_right nat brel_eq_nat bop_times
                                     brel_eq_nat_nontrivial
                                     brel_eq_nat_symmetric
                                     brel_eq_nat_transitive 
                                     bop_times_commutative)


; A_sg_left_cancel_d    := inr _ bop_times_not_left_cancellative
; A_sg_right_cancel_d   := inr _ bop_times_not_right_cancellative
; A_sg_left_constant_d  := inr _ bop_times_not_left_constant
; A_sg_right_constant_d := inr _ bop_times_not_right_constant
; A_sg_anti_left_d      := inr _ bop_times_not_anti_left
; A_sg_anti_right_d     := inr _ bop_times_not_anti_right
|}. 



Definition sg_C_proofs_times : sg_C_proofs nat brel_eq_nat bop_times := 
{| 
  A_sg_C_associative      := bop_times_associative
; A_sg_C_congruence       := bop_times_congruence
; A_sg_C_commutative      := bop_times_commutative
; A_sg_C_selective_d      := inr _ bop_times_not_selective
; A_sg_C_idempotent_d     := inr _ bop_times_not_idempotent 
; A_sg_C_exists_id_d      := inl _ bop_times_exists_id
; A_sg_C_exists_ann_d     := inl _ bop_times_exists_ann
; A_sg_C_left_cancel_d    := inr _ bop_times_not_left_cancellative
; A_sg_C_right_cancel_d   := inr _ bop_times_not_right_cancellative
; A_sg_C_left_constant_d  := inr _ bop_times_not_left_constant
; A_sg_C_right_constant_d := inr _ bop_times_not_right_constant
; A_sg_C_anti_left_d      := inr _ bop_times_not_anti_left
; A_sg_C_anti_right_d     := inr _ bop_times_not_anti_right
|}. 



Definition sg_proofs_plus : sg_proofs nat brel_eq_nat bop_plus := 
{| 
  A_sg_associative      := bop_plus_associative
; A_sg_congruence       := bop_plus_congruence
; A_sg_commutative_d    := inl _ bop_plus_commutative
; A_sg_selective_d      := inr _ bop_plus_not_selective
; A_sg_idempotent_d     := inr _ bop_plus_not_idempotent 
; A_sg_exists_id_d      := inl _ bop_plus_exists_id
; A_sg_exists_ann_d     := inr _ bop_plus_not_exists_ann

; A_sg_is_left_d     := inr _ (bop_commutative_implies_not_is_left nat brel_eq_nat bop_plus
                                     brel_eq_nat_nontrivial
                                     brel_eq_nat_symmetric
                                     brel_eq_nat_transitive 
                                     bop_plus_commutative)
; A_sg_is_right_d   := inr _ (bop_commutative_implies_not_is_right nat brel_eq_nat bop_plus
                                     brel_eq_nat_nontrivial
                                     brel_eq_nat_symmetric
                                     brel_eq_nat_transitive 
                                     bop_plus_commutative)


; A_sg_left_cancel_d    := inl _ bop_plus_left_cancellative 
; A_sg_right_cancel_d   := inl _ bop_plus_right_cancellative 
; A_sg_left_constant_d  := inr _ bop_plus_not_left_constant
; A_sg_right_constant_d := inr _ bop_plus_not_right_constant
; A_sg_anti_left_d      := inr _ bop_plus_not_anti_left
; A_sg_anti_right_d     := inr _ bop_plus_not_anti_right
|}. 


Definition sg_CK_proofs_plus : sg_CK_proofs nat brel_eq_nat bop_plus := 
{| 
  A_sg_CK_associative        := bop_plus_associative
; A_sg_CK_congruence         := bop_plus_congruence
; A_sg_CK_commutative        := bop_plus_commutative
; A_sg_CK_left_cancel        := bop_plus_left_cancellative 
; A_sg_CK_exists_id_d        := inl _ bop_plus_exists_id 
; A_sg_CK_anti_left_d        := inr _ bop_plus_not_anti_left
; A_sg_CK_anti_right_d       := inr _ bop_plus_not_anti_right
|}. 


(* NB : this is cancellative, but not commutative .... 
   want versions of lex to work for this ...
*) 
Definition sg_proofs_concat : 
   ∀ (S : Type) (rS : brel S), 
     eqv_proofs S rS -> sg_proofs (list S) (brel_list S rS) (bop_concat S)
:= λ S rS eqvS, 
{|
  A_sg_associative   := bop_concat_associative S rS (A_eqv_reflexive _ _ eqvS)
; A_sg_congruence    := bop_concat_congruence S rS (A_eqv_reflexive _ _ eqvS)
; A_sg_commutative_d := inr _ (bop_concat_not_commutative S rS (A_eqv_nontrivial _ _ eqvS))
; A_sg_selective_d   := inr _ (bop_concat_not_selective S rS (A_eqv_nontrivial _ _ eqvS))
; A_sg_is_left_d     := inr _ (bop_concat_not_is_left S rS 
                                (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_is_right_d    := inr _ (bop_concat_not_is_right S rS 
                                (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_idempotent_d  := inr _ (bop_concat_not_idempotent S rS 
                                (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_exists_id_d   := inl _ (bop_concat_exists_id S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_exists_ann_d  := inr _ (bop_concat_not_exists_ann S rS 
                                (brel_get_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_left_cancel_d    := inl _ (bop_concat_left_cancellative S rS (A_eqv_reflexive S rS eqvS))
; A_sg_right_cancel_d   := inl _ (bop_concat_right_cancellative S rS)
; A_sg_left_constant_d  := inr _ (bop_concat_not_left_constant S rS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_right_constant_d := inr _ (bop_concat_not_right_constant S rS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_anti_left_d      := inr _ (bop_concat_not_anti_left S rS 
                                   (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_anti_right_d     := inr _ (bop_concat_not_anti_right S rS 
                                   (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
|}. 

Definition sg_proofs_left : ∀ (S : Type) (rS : brel S), 
              (eqv_proofs S rS) → sg_proofs S rS (bop_left S)
:= λ S rS eqvS, 
{| 
  A_sg_associative   := bop_left_associative S rS (A_eqv_reflexive _ _ eqvS)
; A_sg_congruence    := bop_left_congruence S rS 
; A_sg_commutative_d := inr _ (bop_left_not_commutative S rS (A_eqv_nontrivial _ _ eqvS))
; A_sg_selective_d   := inl _ (bop_left_selective S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_is_left_d     := inl _ (bop_left_is_left S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_is_right_d    := inr _ (bop_left_not_is_right S rS (A_eqv_nontrivial _ _ eqvS))
; A_sg_idempotent_d  := inl _ (bop_left_idempotent S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_exists_id_d   := inr _ (bop_left_not_exists_id S rS (A_eqv_nontrivial _ _ eqvS))
; A_sg_exists_ann_d  := inr _ (bop_left_not_exists_ann S rS (A_eqv_nontrivial _ _ eqvS))
; A_sg_left_cancel_d    := inr _ (bop_left_not_left_cancellative S rS
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_nontrivial _ _ eqvS))
; A_sg_right_cancel_d   := inl _ (bop_left_right_cancellative S rS) 
; A_sg_left_constant_d  := inl _ (bop_left_left_constant S rS
                                    (A_eqv_reflexive _ _ eqvS))
; A_sg_right_constant_d := inr _ (bop_left_not_right_constant S rS
                                    (A_eqv_nontrivial _ _ eqvS))
; A_sg_anti_left_d      := inr _ (bop_left_not_anti_left S rS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_anti_right_d     := inr _ (bop_left_not_anti_right S rS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
|}. 


Definition sg_proofs_right : ∀ (S : Type) (rS : brel S), 
              (eqv_proofs S rS) → sg_proofs S rS (bop_right S)
:= λ S rS eqvS, 
{| 
  A_sg_associative   := bop_right_associative S rS (A_eqv_reflexive _ _ eqvS)
; A_sg_congruence    := bop_right_congruence S rS 
; A_sg_commutative_d := inr _ (bop_right_not_commutative S rS (A_eqv_nontrivial _ _ eqvS))
; A_sg_selective_d   := inl _ (bop_right_selective S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_is_left_d     := inr _ (bop_right_not_is_left S rS (A_eqv_nontrivial _ _ eqvS))
; A_sg_is_right_d    := inl _ (bop_right_is_right S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_idempotent_d  := inl _ (bop_right_idempotent S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_exists_id_d   := inr _ (bop_right_not_exists_id S rS (A_eqv_nontrivial _ _ eqvS))
; A_sg_exists_ann_d  := inr _ (bop_right_not_exists_ann S rS (A_eqv_nontrivial _ _ eqvS))
; A_sg_left_cancel_d    := inl _ (bop_right_left_cancellative S rS) 
; A_sg_right_cancel_d   := inr _ (bop_right_not_right_cancellative S rS
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_nontrivial _ _ eqvS))
; A_sg_left_constant_d  := inr _ (bop_right_not_left_constant S rS
                                    (A_eqv_nontrivial _ _ eqvS))
; A_sg_right_constant_d := inl _ (bop_right_right_constant S rS
                                    (A_eqv_reflexive _ _ eqvS))
; A_sg_anti_left_d      := inr _ (bop_right_not_anti_left S rS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_anti_right_d     := inr _ (bop_right_not_anti_right S rS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))

|}. 


(* sg add_id *) 


Definition sg_proofs_add_id : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
     eqv_proofs S rS -> 
     sg_proofs S rS bS -> 
        sg_proofs (with_constant S) (brel_add_constant S rS c) (bop_add_id S bS c)
:= λ S rS c bS eqvS sgS, 
{|
  A_sg_associative   := bop_add_id_associative S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_associative _ _ _ sgS)
; A_sg_congruence    := bop_add_id_congruence S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_congruence _ _ _ sgS) 
; A_sg_commutative_d := bop_add_id_commutative_decide S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_commutative_d _ _ _ sgS)
; A_sg_selective_d   := bop_add_id_selective_decide S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_selective_d _ _ _ sgS)
; A_sg_is_left_d     := inr _ (bop_add_id_not_is_left S rS c bS 
                                (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_is_right_d    := inr _ (bop_add_id_not_is_right S rS c bS 
                                (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_idempotent_d  := bop_add_id_idempotent_decide S rS c bS 
                           (A_sg_idempotent_d _ _ _ sgS)
; A_sg_exists_id_d   := inl _ (bop_add_id_exists_id S rS c bS (A_eqv_reflexive _ _ eqvS))
; A_sg_exists_ann_d  := bop_add_id_exists_ann_decide S rS c bS 
                           (A_eqv_nontrivial _ _ eqvS)
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_exists_ann_d _ _ _ sgS) 
; A_sg_left_cancel_d    :=  bop_add_id_left_cancellative_decide S rS c bS 
                               (A_eqv_symmetric _ _ eqvS)
                               (A_sg_anti_left_d _ _ _ sgS) 
                               (A_sg_left_cancel_d _ _ _ sgS) 
; A_sg_right_cancel_d   := bop_add_id_right_cancellative_decide S rS c bS 
                               (A_eqv_symmetric _ _ eqvS)
                               (A_sg_anti_right_d _ _ _ sgS) 
                               (A_sg_right_cancel_d _ _ _ sgS) 
; A_sg_left_constant_d  := inr _ (bop_add_id_not_left_constant S rS c bS 
                                    (A_eqv_nontrivial _ _ eqvS)) 
; A_sg_right_constant_d := inr _ (bop_add_id_not_right_constant S rS c bS 
                                    (A_eqv_nontrivial _ _ eqvS)) 
; A_sg_anti_left_d      := inr _ (bop_add_id_not_anti_left S rS c bS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_anti_right_d     := inr _ (bop_add_id_not_anti_right S rS c bS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
|}. 



Definition sg_C_proofs_add_id : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
     eqv_proofs S rS -> 
     sg_C_proofs S rS bS -> 
        sg_C_proofs (with_constant S) (brel_add_constant S rS c) (bop_add_id S bS c)
:= λ S rS c bS eqvS sgS, 
{|
  A_sg_C_associative   := bop_add_id_associative S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_C_associative _ _ _ sgS)
; A_sg_C_congruence    := bop_add_id_congruence S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_C_congruence _ _ _ sgS) 
; A_sg_C_commutative   := bop_add_id_commutative S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_C_commutative _ _ _ sgS)
; A_sg_C_selective_d   := bop_add_id_selective_decide S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_C_selective_d _ _ _ sgS)
; A_sg_C_idempotent_d  := bop_add_id_idempotent_decide S rS c bS 
                           (A_sg_C_idempotent_d _ _ _ sgS)
; A_sg_C_exists_id_d   := inl _ (bop_add_id_exists_id S rS c bS (A_eqv_reflexive _ _ eqvS))
; A_sg_C_exists_ann_d  := bop_add_id_exists_ann_decide S rS c bS 
                           (A_eqv_nontrivial _ _ eqvS)
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_C_exists_ann_d _ _ _ sgS) 
; A_sg_C_left_cancel_d    := bop_add_id_left_cancellative_decide  S rS c bS 
                              (A_eqv_symmetric _ _ eqvS)
                              (A_sg_C_anti_left_d _ _ _ sgS) 
                              (A_sg_C_left_cancel_d _ _ _ sgS) 
; A_sg_C_right_cancel_d   := bop_add_id_right_cancellative_decide  S rS c bS 
                              (A_eqv_symmetric _ _ eqvS)
                              (A_sg_C_anti_right_d _ _ _ sgS) 
                              (A_sg_C_right_cancel_d _ _ _ sgS) 
; A_sg_C_left_constant_d  := inr _ (bop_add_id_not_left_constant S rS c bS 
                                    (A_eqv_nontrivial _ _ eqvS))
; A_sg_C_right_constant_d := inr _ (bop_add_id_not_right_constant S rS c bS 
                                    (A_eqv_nontrivial _ _ eqvS))
; A_sg_C_anti_left_d      := inr _ (bop_add_id_not_anti_left S rS c bS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_C_anti_right_d     := inr _ (bop_add_id_not_anti_right S rS c bS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
|}. 

Definition sg_CI_proofs_add_id : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
     eqv_proofs S rS -> 
     sg_CI_proofs S rS bS -> 
        sg_CI_proofs (with_constant S) (brel_add_constant S rS c) (bop_add_id S bS c)
:= λ S rS c bS eqvS sgS, 
{|
  A_sg_CI_associative        := bop_add_id_associative S rS c bS 
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_sg_CI_associative _ _ _ sgS)
; A_sg_CI_congruence         := bop_add_id_congruence S rS c bS 
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_sg_CI_congruence _ _ _ sgS) 
; A_sg_CI_commutative        := bop_add_id_commutative S rS c bS 
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_sg_CI_commutative _ _ _ sgS)
; A_sg_CI_idempotent         := bop_add_id_idempotent S rS c bS 
                                  (A_sg_CI_idempotent _ _ _ sgS)
; A_sg_CI_selective_d        := bop_add_id_selective_decide S rS c bS 
                                 (A_eqv_reflexive _ _ eqvS)
                                 (A_sg_CI_selective_d _ _ _ sgS)
; A_sg_CI_exists_id_d        := inl _ (bop_add_id_exists_id S rS c bS (A_eqv_reflexive _ _ eqvS))
; A_sg_CI_exists_ann_d       := bop_add_id_exists_ann_decide S rS c bS 
                                  (A_eqv_nontrivial _ _ eqvS)
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_sg_CI_exists_ann_d _ _ _ sgS) 
|}. 

Definition sg_CS_proofs_add_id : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
     eqv_proofs S rS -> 
     sg_CS_proofs S rS bS -> 
        sg_CS_proofs (with_constant S) (brel_add_constant S rS c) (bop_add_id S bS c)
:= λ S rS c bS eqvS sgS, 
{|
  A_sg_CS_associative   := bop_add_id_associative S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_CS_associative _ _ _ sgS)
; A_sg_CS_congruence    := bop_add_id_congruence S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_CS_congruence _ _ _ sgS) 
; A_sg_CS_commutative   := bop_add_id_commutative S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_CS_commutative _ _ _ sgS)
; A_sg_CS_selective     := bop_add_id_selective S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_CS_selective _ _ _ sgS)
; A_sg_CS_exists_id_d   := inl _ (bop_add_id_exists_id S rS c bS (A_eqv_reflexive _ _ eqvS))
; A_sg_CS_exists_ann_d  := bop_add_id_exists_ann_decide S rS c bS 
                           (A_eqv_nontrivial _ _ eqvS)
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_CS_exists_ann_d _ _ _ sgS) 
|}.



(* sg add_ann *) 

Definition sg_proofs_add_ann : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
     eqv_proofs S rS -> 
     sg_proofs S rS bS -> 
        sg_proofs (with_constant S) (brel_add_constant S rS c) (bop_add_ann S bS c)
:= λ S rS c bS eqvS sgS, 
{|
  A_sg_associative   := bop_add_ann_associative S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_associative _ _ _ sgS)
; A_sg_congruence    := bop_add_ann_congruence S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_congruence _ _ _ sgS) 
; A_sg_commutative_d := bop_add_ann_commutative_decide S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_commutative_d _ _ _ sgS)
; A_sg_selective_d   := bop_add_ann_selective_decide S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_selective_d _ _ _ sgS)
; A_sg_is_left_d     := inr _ (bop_add_ann_not_is_left S rS c bS 
                                (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_is_right_d    := inr _ (bop_add_ann_not_is_right S rS c bS 
                                (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_idempotent_d  := bop_add_ann_idempotent_decide S rS c bS 
                           (A_sg_idempotent_d _ _ _ sgS)
; A_sg_exists_id_d   := bop_add_ann_exists_id_decide S rS c bS 
                           (A_eqv_nontrivial _ _ eqvS)
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_exists_id_d _ _ _ sgS) 
; A_sg_exists_ann_d  := inl _ (bop_add_ann_exists_ann S rS c bS (A_eqv_reflexive _ _ eqvS))
; A_sg_left_cancel_d    :=  inr _ (bop_add_ann_not_left_cancellative S rS c bS 
                                    (A_eqv_nontrivial _ _ eqvS)) 
; A_sg_right_cancel_d   := inr _ (bop_add_ann_not_right_cancellative S rS c bS 
                                    (A_eqv_nontrivial _ _ eqvS)) 
; A_sg_left_constant_d  := inr _ (bop_add_ann_not_left_constant S rS c bS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_right_constant_d := inr _ (bop_add_ann_not_right_constant S rS c bS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_anti_left_d      := inr _ (bop_add_ann_not_anti_left S rS c bS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_anti_right_d     := inr _ (bop_add_ann_not_anti_right S rS c bS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
|}. 


Definition sg_C_proofs_add_ann : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
     eqv_proofs S rS -> 
     sg_C_proofs S rS bS -> 
        sg_C_proofs (with_constant S) (brel_add_constant S rS c) (bop_add_ann S bS c)
:= λ S rS c bS eqvS sgS, 
{|
  A_sg_C_associative   := bop_add_ann_associative S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_C_associative _ _ _ sgS)
; A_sg_C_congruence    := bop_add_ann_congruence S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_C_congruence _ _ _ sgS) 
; A_sg_C_commutative   := bop_add_ann_commutative S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_C_commutative _ _ _ sgS)
; A_sg_C_selective_d   := bop_add_ann_selective_decide S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_C_selective_d _ _ _ sgS)
; A_sg_C_idempotent_d  := bop_add_ann_idempotent_decide S rS c bS 
                           (A_sg_C_idempotent_d _ _ _ sgS)
; A_sg_C_exists_id_d   := bop_add_ann_exists_id_decide S rS c bS 
                           (A_eqv_nontrivial _ _ eqvS)
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_C_exists_id_d _ _ _ sgS) 
; A_sg_C_exists_ann_d  := inl _ (bop_add_ann_exists_ann S rS c bS 
                               (A_eqv_reflexive _ _ eqvS))

; A_sg_C_left_cancel_d    := inr _ (bop_add_ann_not_left_cancellative  S rS c bS 
                                     (A_eqv_nontrivial _ _ eqvS))
; A_sg_C_right_cancel_d   := inr _ (bop_add_ann_not_right_cancellative  S rS c bS 
                                     (A_eqv_nontrivial _ _ eqvS)) 
; A_sg_C_left_constant_d  := inr _ (bop_add_ann_not_left_constant S rS c bS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_C_right_constant_d := inr _ (bop_add_ann_not_right_constant S rS c bS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_C_anti_left_d      := inr _ (bop_add_ann_not_anti_left S rS c bS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
; A_sg_C_anti_right_d     := inr _ (bop_add_ann_not_anti_right S rS c bS 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS)))
|}. 


Definition sg_CI_proofs_add_ann : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
     eqv_proofs S rS -> 
     sg_CI_proofs S rS bS -> 
        sg_CI_proofs (with_constant S) (brel_add_constant S rS c) (bop_add_ann S bS c)
:= λ S rS c bS eqvS sgS, 
{|
  A_sg_CI_associative        := bop_add_ann_associative S rS c bS 
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_sg_CI_associative _ _ _ sgS)
; A_sg_CI_congruence         := bop_add_ann_congruence S rS c bS 
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_sg_CI_congruence _ _ _ sgS) 
; A_sg_CI_commutative        := bop_add_ann_commutative S rS c bS 
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_sg_CI_commutative _ _ _ sgS)
; A_sg_CI_idempotent         := bop_add_ann_idempotent S rS c bS 
                                  (A_sg_CI_idempotent _ _ _ sgS)
; A_sg_CI_selective_d        := bop_add_ann_selective_decide S rS c bS 
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_sg_CI_selective_d _ _ _ sgS)
; A_sg_CI_exists_id_d        := bop_add_ann_exists_id_decide S rS c bS 
                                  (A_eqv_nontrivial _ _ eqvS)
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_sg_CI_exists_id_d _ _ _ sgS) 
; A_sg_CI_exists_ann_d       := inl _ (bop_add_ann_exists_ann S rS c bS 
                                   (A_eqv_reflexive _ _ eqvS))
|}. 

Definition sg_CS_proofs_add_ann : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S), 
     eqv_proofs S rS -> 
     sg_CS_proofs S rS bS -> 
        sg_CS_proofs (with_constant S) (brel_add_constant S rS c) (bop_add_ann S bS c)
:= λ S rS c bS eqvS sgS, 
{|
  A_sg_CS_associative   := bop_add_ann_associative S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_CS_associative _ _ _ sgS)
; A_sg_CS_congruence    := bop_add_ann_congruence S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_CS_congruence _ _ _ sgS) 
; A_sg_CS_commutative   := bop_add_ann_commutative S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_CS_commutative _ _ _ sgS)
; A_sg_CS_selective   := bop_add_ann_selective S rS c bS 
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_CS_selective _ _ _ sgS)
; A_sg_CS_exists_id_d   := bop_add_ann_exists_id_decide S rS c bS 
                           (A_eqv_nontrivial _ _ eqvS)
                           (A_eqv_reflexive _ _ eqvS)
                           (A_sg_CS_exists_id_d _ _ _ sgS) 
; A_sg_CS_exists_ann_d  := inl _ (bop_add_ann_exists_ann S rS c bS 
                               (A_eqv_reflexive _ _ eqvS))
|}. 


(* semigroup sums *) 

Definition sg_proofs_left_sum : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_proofs S rS bS -> 
     sg_proofs T rT bT -> 
        sg_proofs (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_associative   := bop_left_sum_associative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_associative _ _ _ sgS) 
                         (A_sg_associative _ _ _ sgT) 
; A_sg_congruence    := bop_left_sum_congruence S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_congruence _ _ _ sgS) 
                         (A_sg_congruence _ _ _ sgT) 
; A_sg_commutative_d := bop_left_sum_commutative_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_commutative_d _ _ _ sgS) 
                         (A_sg_commutative_d _ _ _ sgT) 
; A_sg_selective_d   := bop_left_sum_selective_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_selective_d _ _ _ sgS) 
                         (A_sg_selective_d _ _ _ sgT) 
; A_sg_is_left_d     := inr _ (bop_left_sum_not_is_left S T rS rT bS bT 
                         (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                         (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT)))
; A_sg_is_right_d    := inr _ (bop_left_sum_not_is_right S T rS rT bS bT 
                         (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                         (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT)))
; A_sg_idempotent_d  := bop_left_sum_idempotent_decide S T rS rT bS bT 
                         (A_sg_idempotent_d _ _ _ sgS) 
                         (A_sg_idempotent_d _ _ _ sgT) 
; A_sg_exists_id_d   := bop_left_sum_exists_id_decide S T rS rT  bS bT 
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_exists_id_d _ _ _ sgT) 
; A_sg_exists_ann_d  := bop_left_sum_exists_ann_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_exists_ann_d _ _ _ sgS) 
; A_sg_left_cancel_d    := inr _ (bop_left_sum_not_left_cancellative S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (A_eqv_nontrivial _ _ eqvT)
                           ) 
; A_sg_right_cancel_d   := inr _ (bop_left_sum_not_right_cancellative S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (A_eqv_nontrivial _ _ eqvT)
                           ) 
; A_sg_left_constant_d  := inr _ (bop_left_sum_not_left_constant S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                                    (A_eqv_nontrivial _ _ eqvS)
                           ) 
; A_sg_right_constant_d := inr _ (bop_left_sum_not_right_constant S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                                    (A_eqv_nontrivial _ _ eqvS)
                           ) 
; A_sg_anti_left_d      := inr _ (bop_left_sum_not_anti_left S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                           ) 
; A_sg_anti_right_d     := inr _ (bop_left_sum_not_anti_right S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                           ) 
|}. 


Definition sg_C_proofs_left_sum : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_C_proofs S rS bS -> 
     sg_C_proofs T rT bT -> 
        sg_C_proofs (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_C_associative   := bop_left_sum_associative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_C_associative _ _ _ sgS) 
                         (A_sg_C_associative _ _ _ sgT) 
; A_sg_C_congruence    := bop_left_sum_congruence S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_C_congruence _ _ _ sgS) 
                         (A_sg_C_congruence _ _ _ sgT) 
; A_sg_C_commutative := bop_left_sum_commutative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_C_commutative _ _ _ sgS) 
                         (A_sg_C_commutative _ _ _ sgT) 
; A_sg_C_selective_d   := bop_left_sum_selective_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_C_selective_d _ _ _ sgS) 
                         (A_sg_C_selective_d _ _ _ sgT) 
; A_sg_C_idempotent_d  := bop_left_sum_idempotent_decide S T rS rT bS bT 
                         (A_sg_C_idempotent_d _ _ _ sgS) 
                         (A_sg_C_idempotent_d _ _ _ sgT) 
; A_sg_C_exists_id_d   := bop_left_sum_exists_id_decide S T rS rT  bS bT 
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_C_exists_id_d _ _ _ sgT) 
; A_sg_C_exists_ann_d  := bop_left_sum_exists_ann_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_C_exists_ann_d _ _ _ sgS) 
; A_sg_C_left_cancel_d    := inr _ (bop_left_sum_not_left_cancellative S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (A_eqv_nontrivial _ _ eqvT)
                           ) 
; A_sg_C_right_cancel_d   := inr _ (bop_left_sum_not_right_cancellative S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (A_eqv_nontrivial _ _ eqvT)
                           ) 
; A_sg_C_left_constant_d  := inr _ (bop_left_sum_not_left_constant S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                                    (A_eqv_nontrivial _ _ eqvS)
                           ) 
; A_sg_C_right_constant_d := inr _ (bop_left_sum_not_right_constant S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                                    (A_eqv_nontrivial _ _ eqvS)
                           ) 
; A_sg_C_anti_left_d      := inr _ (bop_left_sum_not_anti_left S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                           ) 
; A_sg_C_anti_right_d     := inr _ (bop_left_sum_not_anti_right S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                           ) 
|}. 

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
        sg_C_proofs (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_C_associative   := bop_right_sum_associative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_C_associative _ _ _ sgS) 
                         (A_sg_C_associative _ _ _ sgT) 
; A_sg_C_congruence    := bop_right_sum_congruence S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_C_congruence _ _ _ sgS) 
                         (A_sg_C_congruence _ _ _ sgT) 
; A_sg_C_commutative   := bop_right_sum_commutative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_C_commutative _ _ _ sgS) 
                         (A_sg_C_commutative _ _ _ sgT) 
; A_sg_C_selective_d   := bop_right_sum_selective_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_C_selective_d _ _ _ sgS) 
                         (A_sg_C_selective_d _ _ _ sgT) 
; A_sg_C_idempotent_d  := bop_right_sum_idempotent_decide S T rS rT bS bT 
                         (A_sg_C_idempotent_d _ _ _ sgS) 
                         (A_sg_C_idempotent_d _ _ _ sgT) 
; A_sg_C_exists_id_d   := bop_right_sum_exists_id_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_C_exists_id_d _ _ _ sgS) 
; A_sg_C_exists_ann_d  := bop_right_sum_exists_ann_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_C_exists_ann_d _ _ _ sgT) 
; A_sg_C_left_cancel_d    := inr _ (bop_right_sum_not_left_cancellative S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                                    (A_eqv_nontrivial _ _ eqvS)
                           ) 
; A_sg_C_right_cancel_d   := inr _ (bop_right_sum_not_right_cancellative S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                                    (A_eqv_nontrivial _ _ eqvS)
                           ) 
; A_sg_C_left_constant_d  := inr _ (bop_right_sum_not_left_constant S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (A_eqv_nontrivial _ _ eqvT)
                           ) 
; A_sg_C_right_constant_d := inr _ (bop_right_sum_not_right_constant S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (A_eqv_nontrivial _ _ eqvT)
                           ) 
; A_sg_C_anti_left_d      := inr _ (bop_right_sum_not_anti_left S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                           ) 
; A_sg_C_anti_right_d     := inr _ (bop_right_sum_not_anti_right S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                           ) 
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
        sg_proofs (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_associative   := bop_right_sum_associative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_associative _ _ _ sgS) 
                         (A_sg_associative _ _ _ sgT) 
; A_sg_congruence    := bop_right_sum_congruence S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
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
                         (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                         (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT)))
; A_sg_is_right_d    := inr _ (bop_right_sum_not_is_right S T rS rT bS bT 
                         (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                         (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT)))
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
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                                    (A_eqv_nontrivial _ _ eqvS)
                           ) 
; A_sg_right_cancel_d   := inr _ (bop_right_sum_not_right_cancellative S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                                    (A_eqv_nontrivial _ _ eqvS)
                           ) 
; A_sg_left_constant_d  := inr _ (bop_right_sum_not_left_constant S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (A_eqv_nontrivial _ _ eqvT)
                           ) 
; A_sg_right_constant_d := inr _ (bop_right_sum_not_right_constant S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (A_eqv_nontrivial _ _ eqvT)
                           ) 
; A_sg_anti_left_d      := inr _ (bop_right_sum_not_anti_left S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                           ) 
; A_sg_anti_right_d     := inr _ (bop_right_sum_not_anti_right S T rS rT bS bT 
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvS))
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                           ) 
|}. 

Definition sg_CI_proofs_left_sum : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_CI_proofs S rS bS -> 
     sg_CI_proofs T rT bT -> 
        sg_CI_proofs (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_CI_associative   := bop_left_sum_associative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_CI_associative _ _ _ sgS) 
                         (A_sg_CI_associative _ _ _ sgT) 
; A_sg_CI_congruence    := bop_left_sum_congruence S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_CI_congruence _ _ _ sgS) 
                         (A_sg_CI_congruence _ _ _ sgT) 
; A_sg_CI_commutative := bop_left_sum_commutative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_CI_commutative _ _ _ sgS) 
                         (A_sg_CI_commutative _ _ _ sgT) 
; A_sg_CI_selective_d   := bop_left_sum_selective_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_CI_selective_d _ _ _ sgS) 
                         (A_sg_CI_selective_d _ _ _ sgT) 
; A_sg_CI_idempotent  := bop_left_sum_idempotent S T rS rT bS bT 
                         (A_sg_CI_idempotent _ _ _ sgS) 
                         (A_sg_CI_idempotent _ _ _ sgT) 
; A_sg_CI_exists_id_d   := bop_left_sum_exists_id_decide S T rS rT  bS bT 
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_CI_exists_id_d _ _ _ sgT) 
; A_sg_CI_exists_ann_d  := bop_left_sum_exists_ann_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_CI_exists_ann_d _ _ _ sgS) 
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
        sg_CI_proofs (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_CI_associative   := bop_right_sum_associative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CI_associative _ _ _ sgS) 
                         (A_sg_CI_associative _ _ _ sgT) 
; A_sg_CI_congruence    := bop_right_sum_congruence S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
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



Definition sg_CS_proofs_left_sum : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_CS_proofs S rS bS -> 
     sg_CS_proofs T rT bT -> 
        sg_CS_proofs (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_CS_associative   := bop_left_sum_associative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_CS_associative _ _ _ sgS) 
                         (A_sg_CS_associative _ _ _ sgT) 
; A_sg_CS_congruence    := bop_left_sum_congruence S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_CS_congruence _ _ _ sgT) 
; A_sg_CS_commutative := bop_left_sum_commutative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_CS_commutative _ _ _ sgS) 
                         (A_sg_CS_commutative _ _ _ sgT) 
; A_sg_CS_selective   := bop_left_sum_selective S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sgT) 
; A_sg_CS_exists_id_d   := bop_left_sum_exists_id_decide S T rS rT  bS bT 
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_CS_exists_id_d _ _ _ sgT) 
; A_sg_CS_exists_ann_d  := bop_left_sum_exists_ann_decide S T rS rT bS bT 
                         (A_eqv_nontrivial _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvS)
                         (A_sg_CS_exists_ann_d _ _ _ sgS) 
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
        sg_CS_proofs (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_CS_associative   := bop_right_sum_associative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_associative _ _ _ sgS) 
                         (A_sg_CS_associative _ _ _ sgT) 
; A_sg_CS_congruence    := bop_right_sum_congruence S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
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

(* semigrou products *) 

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
        sg_proofs (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
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
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvT)
                         (A_eqv_transitive _ _ eqvS)
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
                            (A_eqv_nontrivial _ _ eqvT)
                            (A_eqv_reflexive _ _ eqvS)
                            (A_eqv_reflexive _ _ eqvT)
                            (A_sg_left_cancel_d _ _ _ sgS) 
                            (A_sg_left_cancel_d _ _ _ sgT) 
; A_sg_right_cancel_d   := bop_product_right_cancellative_decide S T rS rT bS bT 
                            (A_eqv_nontrivial _ _ eqvS)
                            (A_eqv_nontrivial _ _ eqvT)
                            (A_eqv_reflexive _ _ eqvS)
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
        sg_C_proofs (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
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
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvT)
                         (A_eqv_transitive _ _ eqvS)
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
                            (A_eqv_nontrivial _ _ eqvT)
                            (A_eqv_reflexive _ _ eqvS)
                            (A_eqv_reflexive _ _ eqvT)
                            (A_sg_C_left_cancel_d _ _ _ sgS) 
                            (A_sg_C_left_cancel_d _ _ _ sgT) 
; A_sg_C_right_cancel_d   := bop_product_right_cancellative_decide S T rS rT bS bT 
                            (A_eqv_nontrivial _ _ eqvS)
                            (A_eqv_nontrivial _ _ eqvT)
                            (A_eqv_reflexive _ _ eqvS)
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
        sg_CI_proofs (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
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
                         (A_eqv_nontrivial _ _ eqvT)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvT)
                         (A_eqv_transitive _ _ eqvS)
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
        sg_CK_proofs (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
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



(* semigroup lexicographic *) 

Definition sg_proofs_llex : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_CS_proofs S rS bS -> 
     sg_proofs T rT bT -> 
        sg_proofs (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_associative   := bop_llex_associative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_congruence _ _ eqvS) 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_CS_commutative  S rS bS sgS)
                         (A_sg_CS_selective S rS bS sgS)
                         (A_sg_CS_associative _ _ _ sgS) 
                         (A_sg_associative _ _ _ sgT) 
                         (A_eqv_reflexive _ _ eqvT)
; A_sg_congruence    := bop_llex_congruence S T rS rT bS bT 
                         (A_eqv_congruence _ _ eqvS) 
                         (A_eqv_congruence _ _ eqvT) 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_congruence _ _ _ sgT) 
; A_sg_commutative_d := bop_llex_commutative_decide S T rS rT bS bT    
                         (brel_nontrivial_witness S rS (A_eqv_nontrivial _ _ eqvS))
                         (brel_nontrivial_witness T rT (A_eqv_nontrivial _ _ eqvT))
                         (A_eqv_congruence _ _ eqvS) 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_selective S rS bS sgS)
                         (inl _ (A_sg_CS_commutative S rS bS sgS))
                         (A_sg_commutative_d _ _ _ sgT) 
; A_sg_selective_d   := bop_llex_selective_decide S T rS rT bS bT 
                         (brel_nontrivial_witness S rS (A_eqv_nontrivial _ _ eqvS))
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_congruence _ _ eqvS) 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_CS_commutative S rS bS sgS) 
                         (A_sg_CS_selective S rS bS sgS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_selective_d _ _ _ sgT) 
; A_sg_is_left_d     := inr _ (bop_llex_not_is_left S T rS rT bS bT 
                                 (A_eqv_nontrivial _ _ eqvS)
                                 (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                                 (A_eqv_transitive _ _ eqvS)
                                 (A_eqv_symmetric _ _ eqvS)
                                 (A_sg_CS_commutative S rS bS sgS) 
                                 (A_sg_CS_selective S rS bS sgS)
                              )
; A_sg_is_right_d    := inr _ (bop_llex_not_is_right S T rS rT bS bT 
                                 (A_eqv_nontrivial _ _ eqvS)
                                 (brel_nontrivial_witness T _ (A_eqv_nontrivial _ _ eqvT))
                                 (A_eqv_transitive _ _ eqvS)
                                 (A_eqv_symmetric _ _ eqvS)
                                 (A_sg_CS_commutative S rS bS sgS)
                                 (A_sg_CS_selective S rS bS sgS) 
                              )
; A_sg_idempotent_d  := bop_llex_idempotent_decide S T rS rT bS bT 
                         (brel_nontrivial_witness S rS (A_eqv_nontrivial _ _ eqvS))
                         (brel_nontrivial_witness T rT (A_eqv_nontrivial _ _ eqvT))
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (inl _(bop_selective_implies_idempotent S rS bS (A_sg_CS_selective S rS bS sgS)))
                         (A_sg_idempotent_d _ _ _ sgT) 
; A_sg_exists_id_d   := bop_llex_exists_id_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_commutative S rS bS sgS) 
                         (A_sg_CS_exists_id_d _ _ _ sgS) 
                         (A_sg_exists_id_d _ _ _ sgT) 
; A_sg_exists_ann_d  :=  bop_llex_exists_ann_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_commutative S rS bS sgS) 
                         (A_sg_CS_exists_ann_d _ _ _ sgS) 
                         (A_sg_exists_ann_d _ _ _ sgT) 
; A_sg_left_cancel_d    := inr _ (bop_llex_not_left_cancellative_v2 S T rS rT bS bT 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_nontrivial _ _ eqvT)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_CS_congruence _ _ _ sgS)
                                    (A_sg_CS_selective S rS bS sgS)
                                    (A_sg_CS_commutative S rS bS sgS) 
                                    (A_eqv_reflexive _ _ eqvT)
                           ) 
; A_sg_right_cancel_d   := inr _ (bop_llex_not_right_cancellative S T rS rT bS bT 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_nontrivial _ _ eqvT)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_CS_congruence _ _ _ sgS)
                                    (A_sg_CS_selective S rS bS sgS)
                                    (A_sg_CS_commutative S rS bS sgS) 
                                    (A_eqv_reflexive _ _ eqvT)
                           ) 
; A_sg_left_constant_d  := inr _ (bop_llex_not_left_constant S T rS rT bS bT 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_nontrivial _ _ eqvT)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_CS_congruence _ _ _ sgS)
                                    (A_sg_CS_selective S rS bS sgS) 
                                    (A_sg_CS_commutative S rS bS sgS) 
                                    (A_eqv_reflexive _ _ eqvT)
                           ) 
; A_sg_right_constant_d := inr _ (bop_llex_not_right_constant S T rS rT bS bT 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_nontrivial _ _ eqvT)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_CS_congruence _ _ _ sgS)
                                    (A_sg_CS_selective S rS bS sgS)
                                    (A_sg_CS_commutative S rS bS sgS) 
                                    (A_eqv_reflexive _ _ eqvT)
                           ) 
; A_sg_anti_left_d      := inr _ (bop_llex_not_anti_left S T rS rT bS bT 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_CS_selective S rS bS sgS) 
                                    (A_sg_CS_commutative S rS bS sgS) 
                                    (A_eqv_reflexive _ _ eqvT)
                           ) 
; A_sg_anti_right_d     := inr _ (bop_llex_not_anti_right S T rS rT bS bT 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_CS_selective S rS bS sgS)
                                    (A_sg_CS_commutative S rS bS sgS) 
                                    (A_eqv_reflexive _ _ eqvT)
                           ) 
|}. 


Definition sg_C_proofs_llex : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_CS_proofs S rS bS -> 
     sg_C_proofs T rT bT -> 
        sg_C_proofs (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sg_CT, 
{|
  A_sg_C_associative   := bop_llex_associative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_congruence _ _ eqvS) 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_CS_commutative _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_sg_CS_associative _ _ _ sgS) 
                         (A_sg_C_associative _ _ _ sg_CT) 
                         (A_eqv_reflexive _ _ eqvT)
; A_sg_C_congruence    := bop_llex_congruence S T rS rT bS bT 
                         (A_eqv_congruence _ _ eqvS) 
                         (A_eqv_congruence _ _ eqvT) 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_C_congruence _ _ _ sg_CT) 
; A_sg_C_commutative := bop_llex_commutative S T rS rT bS bT    
                         (A_eqv_congruence _ _ eqvS) 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_sg_CS_commutative _ _ _ sgS)
                         (A_sg_C_commutative _ _ _ sg_CT) 
; A_sg_C_selective_d   := bop_llex_selective_decide S T rS rT bS bT 
                         (brel_nontrivial_witness S rS (A_eqv_nontrivial _ _ eqvS))
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_congruence _ _ eqvS) 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_CS_commutative _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_C_selective_d _ _ _ sg_CT) 
; A_sg_C_idempotent_d  := bop_llex_idempotent_decide S T rS rT bS bT 
                         (brel_nontrivial_witness S rS (A_eqv_nontrivial _ _ eqvS))
                         (brel_nontrivial_witness T rT (A_eqv_nontrivial _ _ eqvT))
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (inl _(bop_selective_implies_idempotent S rS bS 
                                  (A_sg_CS_selective _ _ _ sgS)))
                         (A_sg_C_idempotent_d _ _ _ sg_CT) 
; A_sg_C_exists_id_d   := bop_llex_exists_id_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_commutative _ _ _ sgS)
                         (A_sg_CS_exists_id_d _ _ _ sgS) 
                         (A_sg_C_exists_id_d _ _ _ sg_CT) 
; A_sg_C_exists_ann_d  :=  bop_llex_exists_ann_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_commutative _ _ _ sgS)
                         (A_sg_CS_exists_ann_d _ _ _ sgS) 
                         (A_sg_C_exists_ann_d _ _ _ sg_CT) 
; A_sg_C_left_cancel_d    := inr _ (bop_llex_not_left_cancellative_v2 S T rS rT bS bT 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_nontrivial _ _ eqvT)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_CS_congruence _ _ _ sgS)
                                    (A_sg_CS_selective _ _ _ sgS)
                                    (A_sg_CS_commutative _ _ _ sgS)
                                    (A_eqv_reflexive _ _ eqvT)
                           ) 
; A_sg_C_right_cancel_d   := inr _ (bop_llex_not_right_cancellative S T rS rT bS bT 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_nontrivial _ _ eqvT)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_CS_congruence _ _ _ sgS)
                                    (A_sg_CS_selective _ _ _ sgS)
                                    (A_sg_CS_commutative _ _ _ sgS)
                                    (A_eqv_reflexive _ _ eqvT)
                           ) 
; A_sg_C_left_constant_d  := inr _ (bop_llex_not_left_constant S T rS rT bS bT 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_nontrivial _ _ eqvT)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_CS_congruence _ _ _ sgS)
                                    (A_sg_CS_selective _ _ _ sgS)
                                    (A_sg_CS_commutative _ _ _ sgS)
                                    (A_eqv_reflexive _ _ eqvT)
                           ) 
; A_sg_C_right_constant_d := inr _ (bop_llex_not_right_constant S T rS rT bS bT 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_nontrivial _ _ eqvT)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_CS_congruence _ _ _ sgS)
                                    (A_sg_CS_selective _ _ _ sgS)
                                    (A_sg_CS_commutative _ _ _ sgS)
                                    (A_eqv_reflexive _ _ eqvT)
                           ) 
; A_sg_C_anti_left_d      := inr _ (bop_llex_not_anti_left S T rS rT bS bT 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_CS_selective _ _ _ sgS)
                                    (A_sg_CS_commutative _ _ _ sgS)
                                    (A_eqv_reflexive _ _ eqvT)
                           ) 
; A_sg_C_anti_right_d     := inr _ (bop_llex_not_anti_right S T rS rT bS bT 
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (brel_nontrivial_witness _ _ (A_eqv_nontrivial _ _ eqvT))
                                    (A_eqv_symmetric _ _ eqvS)
                                    (A_eqv_transitive _ _ eqvS)
                                    (A_sg_CS_selective _ _ _ sgS)
                                    (A_sg_CS_commutative _ _ _ sgS)
                                    (A_eqv_reflexive _ _ eqvT)
                           ) 

|}. 


Definition sg_CI_proofs_llex : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_CS_proofs S rS bS -> 
     sg_CI_proofs T rT bT -> 
        sg_CI_proofs (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sg_CIT, 
{|
  A_sg_CI_associative   := bop_llex_associative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_congruence _ _ eqvS) 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_CS_commutative _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_sg_CS_associative _ _ _ sgS) 
                         (A_sg_CI_associative _ _ _ sg_CIT) 
                         (A_eqv_reflexive _ _ eqvT)
; A_sg_CI_congruence    := bop_llex_congruence S T rS rT bS bT 
                         (A_eqv_congruence _ _ eqvS) 
                         (A_eqv_congruence _ _ eqvT) 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_CI_congruence _ _ _ sg_CIT) 
; A_sg_CI_commutative := bop_llex_commutative S T rS rT bS bT    
                         (A_eqv_congruence _ _ eqvS) 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_sg_CS_commutative _ _ _ sgS)
                         (A_sg_CI_commutative _ _ _ sg_CIT) 
; A_sg_CI_idempotent   := bop_llex_idempotent S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (bop_selective_implies_idempotent S rS bS 
                                  (A_sg_CS_selective _ _ _ sgS))
                         (A_sg_CI_idempotent _ _ _ sg_CIT) 
; A_sg_CI_selective_d   := bop_llex_selective_decide S T rS rT bS bT 
                         (brel_nontrivial_witness S rS (A_eqv_nontrivial _ _ eqvS))
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_congruence _ _ eqvS) 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_CS_commutative _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CI_selective_d _ _ _ sg_CIT) 
; A_sg_CI_exists_id_d   := bop_llex_exists_id_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_commutative _ _ _ sgS)
                         (A_sg_CS_exists_id_d _ _ _ sgS) 
                         (A_sg_CI_exists_id_d _ _ _ sg_CIT) 
; A_sg_CI_exists_ann_d  :=  bop_llex_exists_ann_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_commutative _ _ _ sgS)
                         (A_sg_CS_exists_ann_d _ _ _ sgS) 
                         (A_sg_CI_exists_ann_d _ _ _ sg_CIT) 
|}. 


Definition sg_CS_proofs_llex : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_CS_proofs S rS bS -> 
     sg_CS_proofs T rT bT -> 
        sg_CS_proofs (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sg_CST, 
{|
  A_sg_CS_associative   := bop_llex_associative S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_congruence _ _ eqvS) 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_CS_commutative _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_sg_CS_associative _ _ _ sgS) 
                         (A_sg_CS_associative _ _ _ sg_CST) 
                         (A_eqv_reflexive _ _ eqvT)
; A_sg_CS_congruence    := bop_llex_congruence S T rS rT bS bT 
                         (A_eqv_congruence _ _ eqvS) 
                         (A_eqv_congruence _ _ eqvT) 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_CS_congruence _ _ _ sg_CST) 
; A_sg_CS_commutative := bop_llex_commutative S T rS rT bS bT    
                         (A_eqv_congruence _ _ eqvS) 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_sg_CS_commutative _ _ _ sgS)
                         (A_sg_CS_commutative _ _ _ sg_CST) 
; A_sg_CS_selective   := bop_llex_selective S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_eqv_congruence _ _ eqvS) 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_CS_commutative _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sg_CST) 
; A_sg_CS_exists_id_d   := bop_llex_exists_id_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_commutative _ _ _ sgS)
                         (A_sg_CS_exists_id_d _ _ _ sgS) 
                         (A_sg_CS_exists_id_d _ _ _ sg_CST) 
; A_sg_CS_exists_ann_d  :=  bop_llex_exists_ann_decide S T rS rT bS bT 
                         (A_eqv_reflexive _ _ eqvS)
                         (A_eqv_symmetric _ _ eqvS)
                         (A_eqv_transitive _ _ eqvS)
                         (A_eqv_reflexive _ _ eqvT)
                         (A_sg_CS_commutative _ _ _ sgS)
                         (A_sg_CS_exists_ann_d _ _ _ sgS) 
                         (A_sg_CS_exists_ann_d _ _ _ sg_CST) 
|}. 



(* SETS *) 
(***********************************)


Definition sg_proofs_union : 
   ∀ (S : Type) (r : brel S) (c : cas_constant), eqv_proofs S r -> 
        sg_proofs (with_constant (finite_set S)) 
                  (brel_add_constant (finite_set S) (brel_set S r) c) 
                  (bop_add_ann (finite_set S) (bop_union S r) c)
:= λ S r c eqvS, 
{|
  A_sg_associative   := bop_union_associative S r c
                           (A_eqv_reflexive _ _ eqvS)
                           (A_eqv_symmetric _ _ eqvS) 
                           (A_eqv_transitive _ _ eqvS)
; A_sg_congruence    := bop_union_congruence S r c
                           (A_eqv_reflexive _ _ eqvS)
                           (A_eqv_symmetric _ _ eqvS) 
                           (A_eqv_transitive _ _ eqvS) 
; A_sg_commutative_d   := inl _ (bop_union_commutative S r c
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS))
; A_sg_idempotent_d  := inl _ (bop_union_idempotent S r c
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_eqv_symmetric _ _ eqvS) 
                                  (A_eqv_transitive _ _ eqvS))
; A_sg_selective_d   := inr _ (bop_union_not_selective S r c
                                    (A_eqv_nontrivial _ _ eqvS)
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_eqv_symmetric _ _ eqvS)) 
; A_sg_exists_id_d   := inl _ (bop_union_exists_id S r c
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_eqv_symmetric _ _ eqvS) 
                                  (A_eqv_transitive _ _ eqvS))
; A_sg_exists_ann_d     := inl _ (bop_union_exists_ann S r c
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_eqv_symmetric _ _ eqvS) 
                                  (A_eqv_transitive _ _ eqvS))
; A_sg_is_left_d        := inr _ (bop_union_not_is_left S r c
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS)) 
; A_sg_is_right_d       := inr _ (bop_union_not_is_right S r c
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS)) 
; A_sg_left_cancel_d    := inr _ (bop_union_not_left_cancellative S r c
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS))  
; A_sg_right_cancel_d   := inr _ (bop_union_not_right_cancellative S r c
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS))  
; A_sg_left_constant_d  := inr _ (bop_union_not_left_constant S r c
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS))  
; A_sg_right_constant_d := inr _ (bop_union_not_right_constant S r c
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS))  
; A_sg_anti_left_d      := inr _ (bop_union_not_anti_left S r c
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS))
; A_sg_anti_right_d     := inr _ (bop_union_not_anti_right S r c
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS))
|}. 



Definition sg_proofs_intersect : 
   ∀ (S : Type) (r : brel S) (c : cas_constant), eqv_proofs S r -> 
        sg_proofs (with_constant (finite_set S)) 
                  (brel_add_constant (finite_set S) (brel_set S r) c) 
                  (bop_add_id (finite_set S) (bop_intersect S r) c)
:= λ S r c eqvS, 
{|
  A_sg_associative   := bop_intersect_associative S r c
                           (A_eqv_reflexive _ _ eqvS)
                           (A_eqv_symmetric _ _ eqvS) 
                           (A_eqv_transitive _ _ eqvS)
; A_sg_congruence    := bop_intersect_congruence S r c
                           (A_eqv_reflexive _ _ eqvS)
                           (A_eqv_symmetric _ _ eqvS) 
                           (A_eqv_transitive _ _ eqvS) 
; A_sg_commutative_d   := inl _ (bop_intersect_commutative S r c
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS))
; A_sg_idempotent_d  := inl _ (bop_intersect_idempotent S r c
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_eqv_symmetric _ _ eqvS) 
                                  (A_eqv_transitive _ _ eqvS))
; A_sg_selective_d   := inr _ (bop_intersect_not_selective S r c
                                  (A_eqv_nontrivial _ _ eqvS)
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_eqv_symmetric _ _ eqvS))
; A_sg_exists_id_d   := inl _ (bop_intersect_exists_id S r c
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_eqv_symmetric _ _ eqvS) 
                                  (A_eqv_transitive _ _ eqvS))
; A_sg_exists_ann_d     := inl _ (bop_intersect_exists_ann S r c 
                                  (A_eqv_reflexive _ _ eqvS)
                                  (A_eqv_symmetric _ _ eqvS) 
                                  (A_eqv_transitive _ _ eqvS))
; A_sg_is_left_d        := inr _ (bop_intersect_not_is_left S r c
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS)) 
; A_sg_is_right_d       := inr _ (bop_intersect_not_is_right S r c
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS)) 
; A_sg_left_cancel_d    := inr _ (bop_intersect_not_left_cancellative S r c
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS))  
; A_sg_right_cancel_d   := inr _ (bop_intersect_not_right_cancellative S r c
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS))  
; A_sg_left_constant_d  := inr _ (bop_intersect_not_left_constant S r c
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS))  
; A_sg_right_constant_d := inr _ (bop_intersect_not_right_constant S r c
                                    (A_eqv_nontrivial _ _ eqvS)
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS))  
; A_sg_anti_left_d      := inr _ (bop_intersect_not_anti_left S r c
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS))
; A_sg_anti_right_d     := inr _ (bop_intersect_not_anti_right S r c
                                    (A_eqv_reflexive _ _ eqvS)
                                    (A_eqv_symmetric _ _ eqvS) 
                                    (A_eqv_transitive _ _ eqvS))
|}. 


(*
Definition sg_CI_proofs_union : 
   ∀ (S : Type) (r : brel S) (c : cas_constant), 
     eqv_proofs S r -> 
        sg_CI_proofs (with_constant (finite_set S)) 
                    (brel_add_constant (finite_set S) (brel_set S r) c) 
                    (bop_add_ann (finite_set S) (bop_union S r) c)
:= λ S r c eqvS, 
{|
  A_sg_CI_associative   := bop_add_ann_associative (finite_set S) (brel_set S r) c 
                           (bop_union S r) 
                           (brel_set_reflexive S r 
                              (A_eqv_reflexive _ _ eqvS)
                              (A_eqv_symmetric _ _ eqvS) 
                              (A_eqv_transitive _ _ eqvS) 
                           )
                           (bop_union_associative S r
                              (A_eqv_reflexive _ _ eqvS)
                              (A_eqv_symmetric _ _ eqvS) 
                              (A_eqv_transitive _ _ eqvS) 
                          ) 
; A_sg_CI_congruence    := bop_add_ann_congruence (finite_set S) (brel_set S r) c 
                           (bop_union S r) 
                           (brel_set_reflexive S r 
                              (A_eqv_reflexive _ _ eqvS)
                              (A_eqv_symmetric _ _ eqvS) 
                              (A_eqv_transitive _ _ eqvS) 
                           )
                           (bop_union_congruence S r 
                              (A_eqv_reflexive _ _ eqvS)
                              (A_eqv_symmetric _ _ eqvS) 
                              (A_eqv_transitive _ _ eqvS) 
                           ) 
; A_sg_CI_commutative   := bop_add_ann_commutative (finite_set S) (brel_set S r) c 
                           (bop_union S r) 
                           (brel_set_reflexive S r 
                              (A_eqv_reflexive _ _ eqvS)
                              (A_eqv_symmetric _ _ eqvS) 
                              (A_eqv_transitive _ _ eqvS) 
                           )
                           (bop_union_commutative S r 
                              (A_eqv_reflexive _ _ eqvS)
                              (A_eqv_symmetric _ _ eqvS) 
                              (A_eqv_transitive _ _ eqvS) 
                           ) 
; A_sg_CI_idempotent    := bop_add_ann_idempotent (finite_set S) (brel_set S r) c 
                           (bop_union S r) 
                           (bop_union_idempotent S r 
                              (A_eqv_reflexive _ _ eqvS)
                              (A_eqv_symmetric _ _ eqvS) 
                              (A_eqv_transitive _ _ eqvS) 
                           ) 
; A_sg_CI_selective_d   := inr _ (bop_add_ann_not_selective (finite_set S) (brel_set S r) c 
                                   (bop_union S r) 
                                   (bop_union_not_selective S r 
                                      (A_eqv_reflexive _ _ eqvS)
                                      (A_eqv_symmetric _ _ eqvS) 
                                      (A_eqv_nontrivial _ _ eqvS) 
                                   )
                                )
; A_sg_CI_exists_id_d   := inl _ (bop_add_ann_exists_id (finite_set S) (brel_set S r) c 
                                   (bop_union S r) 
                                   (brel_set_reflexive S r 
                                      (A_eqv_reflexive _ _ eqvS)
                                      (A_eqv_symmetric _ _ eqvS) 
                                      (A_eqv_transitive _ _ eqvS) 
                                    )
                                   (bop_union_exists_id S r 
                                     (A_eqv_reflexive _ _ eqvS)
                                     (A_eqv_symmetric _ _ eqvS) 
                                     (A_eqv_transitive _ _ eqvS) 
                                   ) 
                                )
; A_sg_CI_exists_ann_d  := inl _ (bop_add_ann_exists_ann (finite_set S) (brel_set S r) c 
                                   (bop_union S r) 
                                   (brel_set_reflexive S r 
                                      (A_eqv_reflexive _ _ eqvS)
                                      (A_eqv_symmetric _ _ eqvS) 
                                      (A_eqv_transitive _ _ eqvS) 
                                    )
                                 )
|}. 


Definition sg_CI_proofs_intersect_with_id : 
   ∀ (S : Type) (r : brel S) (c : cas_constant), 
     eqv_proofs S r -> 
        sg_CI_proofs (with_constant (finite_set S)) 
                    (brel_add_constant (finite_set S) (brel_set S r) c) 
                    (bop_add_id (finite_set S) (bop_intersect S r) c)
:= λ S r c eqvS, 
{|
  A_sg_CI_associative   := bop_add_id_associative (finite_set S) (brel_set S r) c 
                           (bop_intersect S r) 
                           (brel_set_reflexive S r 
                              (A_eqv_reflexive _ _ eqvS)
                              (A_eqv_symmetric _ _ eqvS) 
                              (A_eqv_transitive _ _ eqvS) 
                           )
                           (bop_intersect_associative S r
                              (A_eqv_reflexive _ _ eqvS)
                              (A_eqv_symmetric _ _ eqvS) 
                              (A_eqv_transitive _ _ eqvS) 
                          ) 
; A_sg_CI_congruence    := bop_add_id_congruence (finite_set S) (brel_set S r) c 
                           (bop_intersect S r) 
                           (brel_set_reflexive S r 
                              (A_eqv_reflexive _ _ eqvS)
                              (A_eqv_symmetric _ _ eqvS) 
                              (A_eqv_transitive _ _ eqvS) 
                           )
                           (bop_intersect_congruence S r 
                              (A_eqv_reflexive _ _ eqvS)
                              (A_eqv_symmetric _ _ eqvS) 
                              (A_eqv_transitive _ _ eqvS) 
                           ) 
; A_sg_CI_commutative   := bop_add_id_commutative (finite_set S) (brel_set S r) c 
                           (bop_intersect S r) 
                           (brel_set_reflexive S r 
                              (A_eqv_reflexive _ _ eqvS)
                              (A_eqv_symmetric _ _ eqvS) 
                              (A_eqv_transitive _ _ eqvS) 
                           )
                           (bop_intersect_commutative S r 
                              (A_eqv_reflexive _ _ eqvS)
                              (A_eqv_symmetric _ _ eqvS) 
                              (A_eqv_transitive _ _ eqvS) 
                           ) 
; A_sg_CI_idempotent    := bop_add_id_idempotent (finite_set S) (brel_set S r) c 
                           (bop_intersect S r) 
                           (bop_intersect_idempotent S r 
                              (A_eqv_reflexive _ _ eqvS)
                              (A_eqv_symmetric _ _ eqvS) 
                              (A_eqv_transitive _ _ eqvS) 
                           ) 
; A_sg_CI_selective_d   := inr _ (bop_add_id_not_selective (finite_set S) (brel_set S r) c 
                                   (bop_intersect S r) 
                                   (bop_intersect_not_selective S r 
                                      (A_eqv_reflexive _ _ eqvS)
                                      (A_eqv_symmetric _ _ eqvS) 
                                      (A_eqv_nontrivial _ _ eqvS) 
                                   )
                                )
; A_sg_CI_exists_id_d   := inl _ (bop_add_id_exists_id (finite_set S) (brel_set S r) c 
                                   (bop_intersect S r) 
                                   (brel_set_reflexive S r 
                                      (A_eqv_reflexive _ _ eqvS)
                                      (A_eqv_symmetric _ _ eqvS) 
                                      (A_eqv_transitive _ _ eqvS) 
                                    )
                                 )
; A_sg_CI_exists_ann_d  := inl _ (bop_add_id_exists_ann (finite_set S) (brel_set S r) c 
                                   (bop_intersect S r) 
                                   (brel_set_reflexive S r 
                                      (A_eqv_reflexive _ _ eqvS)
                                      (A_eqv_symmetric _ _ eqvS) 
                                      (A_eqv_transitive _ _ eqvS) 
                                    )
                                   (bop_intersect_exists_ann S r 
                                     (A_eqv_reflexive _ _ eqvS)
                                     (A_eqv_symmetric _ _ eqvS) 
                                     (A_eqv_transitive _ _ eqvS) 
                                   ) 
                                )
|}. 

*) 

(***********************************)



Definition bs_proofs_and_or : bs_proofs bool  brel_eq_bool bop_and bop_or := 
  {| 
     A_bs_left_distributive_d      := inl _ bops_and_or_left_distributive
   ; A_bs_right_distributive_d     := inl _ bops_and_or_right_distributive
   ; A_bs_plus_id_is_times_ann_d   := inl _ bops_and_or_id_equals_ann
   ; A_bs_times_id_is_plus_ann_d   := inl _ bops_and_or_ann_equals_id 
   ; A_bs_left_left_absorptive_d   := inl _ bops_and_or_left_left_absorptive
   ; A_bs_left_right_absorptive_d  := inl _ bops_and_or_left_right_absorptive
   ; A_bs_right_left_absorptive_d  := inl _ bops_and_or_right_left_absorptive
   ; A_bs_right_right_absorptive_d := inl _ bops_and_or_right_right_absorptive
  |}. 


Definition bs_proofs_or_and : bs_proofs bool  brel_eq_bool bop_or bop_and := 
  {| 
     A_bs_left_distributive_d      := inl _ bops_or_and_left_distributive
   ; A_bs_right_distributive_d     := inl _ bops_or_and_right_distributive
   ; A_bs_plus_id_is_times_ann_d   := inl _ bops_or_and_id_equals_ann
   ; A_bs_times_id_is_plus_ann_d   := inl _ bops_or_and_ann_equals_id 
   ; A_bs_left_left_absorptive_d   := inl _ bops_or_and_left_left_absorptive
   ; A_bs_left_right_absorptive_d  := inl _ bops_or_and_left_right_absorptive
   ; A_bs_right_left_absorptive_d  := inl _ bops_or_and_right_left_absorptive
   ; A_bs_right_right_absorptive_d := inl _ bops_or_and_right_right_absorptive
  |}. 


Definition bs_proofs_max_min : bs_proofs nat brel_eq_nat bop_max bop_min := 
  {| 
     A_bs_left_distributive_d      := inl _ bops_max_min_left_distributive
   ; A_bs_right_distributive_d     := inl _ bops_max_min_right_distributive
   ; A_bs_plus_id_is_times_ann_d   := inl _ bops_max_min_id_equals_ann
   ; A_bs_times_id_is_plus_ann_d   := inr _ bops_max_min_not_ann_equals_id 
   ; A_bs_left_left_absorptive_d   := inl _ bops_max_min_left_left_absorptive
   ; A_bs_left_right_absorptive_d  := inl _ bops_max_min_left_right_absorptive
   ; A_bs_right_left_absorptive_d  := inl _ bops_max_min_right_left_absorptive
   ; A_bs_right_right_absorptive_d := inl _ bops_max_min_right_right_absorptive
  |}. 

Definition bs_proofs_min_max : bs_proofs nat brel_eq_nat bop_min bop_max := 
  {| 
     A_bs_left_distributive_d      := inl _ bops_min_max_left_distributive
   ; A_bs_right_distributive_d     := inl _ bops_min_max_right_distributive
   ; A_bs_plus_id_is_times_ann_d   := inr _ bops_min_max_not_id_equals_ann
   ; A_bs_times_id_is_plus_ann_d   := inl _ bops_min_max_ann_equals_id 
   ; A_bs_left_left_absorptive_d   := inl _ bops_min_max_left_left_absorptive
   ; A_bs_left_right_absorptive_d  := inl _ bops_min_max_left_right_absorptive
   ; A_bs_right_left_absorptive_d  := inl _ bops_min_max_right_left_absorptive
   ; A_bs_right_right_absorptive_d := inl _ bops_min_max_right_right_absorptive
  |}. 


Definition bs_proofs_min_plus : bs_proofs nat brel_eq_nat bop_min bop_plus := 
  {| 
     A_bs_left_distributive_d      := inl _ bop_min_plus_left_distributive
   ; A_bs_right_distributive_d     := inl _ bop_min_plus_right_distributive

   ; A_bs_plus_id_is_times_ann_d   := inr _ bop_min_plus_not_id_equals_ann
   ; A_bs_times_id_is_plus_ann_d   := inl _ bop_min_plus_ann_equals_id 

   ; A_bs_left_left_absorptive_d   := inl _ bops_min_plus_left_left_absorptive
   ; A_bs_left_right_absorptive_d  := inl _ bops_min_plus_left_right_absorptive
   ; A_bs_right_left_absorptive_d  := inl _ bops_min_plus_right_left_absorptive
   ; A_bs_right_right_absorptive_d := inl _ bops_min_plus_right_right_absorptive
  |}. 


Definition bs_proofs_max_plus : bs_proofs nat brel_eq_nat bop_max bop_plus := 
  {| 
     A_bs_left_distributive_d      := inl _ bop_max_plus_left_distributive
   ; A_bs_right_distributive_d     := inl _ bop_max_plus_right_distributive

   ; A_bs_plus_id_is_times_ann_d   := inr _ bop_max_plus_not_id_equals_ann
   ; A_bs_times_id_is_plus_ann_d   := inr _ bop_plus_max_not_id_equals_ann

   ; A_bs_left_left_absorptive_d   := inr _ bops_max_plus_not_left_left_absorptive
   ; A_bs_left_right_absorptive_d  := inr _ bops_max_plus_not_left_right_absorptive
   ; A_bs_right_left_absorptive_d  := inr _ bops_max_plus_not_right_left_absorptive
   ; A_bs_right_right_absorptive_d := inr _ bops_max_plus_not_right_right_absorptive
  |}. 



Definition bs_proofs_add_one : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (plusS timesS : binary_op S), 
     eqv_proofs S rS -> 
     sg_proofs S rS plusS -> 
     bs_proofs S rS plusS timesS -> 
        bs_proofs 
           (with_constant S) 
           (brel_add_constant S rS c)
           (bop_add_ann S plusS c)
           (bop_add_id S timesS c)
:= λ S rS c plusS timesS eqvS ppS pS, 
{|
  A_bs_left_distributive_d    := 
     bops_add_one_left_distributive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (A_sg_idempotent_d S rS plusS ppS)
        (A_bs_left_left_absorptive_d S rS plusS timesS pS)
        (A_bs_right_left_absorptive_d S rS plusS timesS pS)
        (A_bs_left_distributive_d S rS plusS timesS pS) 
; A_bs_right_distributive_d   := 
     bops_add_one_right_distributive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (A_sg_idempotent_d S rS plusS ppS)
        (A_bs_left_right_absorptive_d S rS plusS timesS pS)
        (A_bs_right_right_absorptive_d S rS plusS timesS pS)
        (A_bs_right_distributive_d S rS plusS timesS pS) 
; A_bs_left_left_absorptive_d      := 
     bops_add_one_left_left_absorptive_decide S rS c plusS timesS 
        (A_eqv_symmetric S rS eqvS)
        (A_sg_idempotent_d S rS plusS ppS)
        (A_bs_left_left_absorptive_d S rS plusS timesS pS)
; A_bs_left_right_absorptive_d      := 
     bops_add_one_left_right_absorptive_decide S rS c plusS timesS 
        (A_eqv_symmetric S rS eqvS)
        (A_sg_idempotent_d S rS plusS ppS)
        (A_bs_left_right_absorptive_d S rS plusS timesS pS)
; A_bs_right_left_absorptive_d     := 
     bops_add_one_right_left_absorptive_decide S rS c plusS timesS 
        (A_eqv_symmetric S rS eqvS)
        (A_sg_idempotent_d S rS plusS ppS)
        (A_bs_right_left_absorptive_d S rS plusS timesS pS)
; A_bs_right_right_absorptive_d     := 
     bops_add_one_right_right_absorptive_decide S rS c plusS timesS 
        (A_eqv_symmetric S rS eqvS)
        (A_sg_idempotent_d S rS plusS ppS)
        (A_bs_right_right_absorptive_d S rS plusS timesS pS)
; A_bs_plus_id_is_times_ann_d := 
    bops_add_one_id_equals_ann_decide S rS 
      (brel_get_witness S rS (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS)))
      c plusS timesS 
      (A_eqv_reflexive S rS eqvS)
      (A_bs_plus_id_is_times_ann_d S rS plusS timesS pS)

; A_bs_times_id_is_plus_ann_d :=  
     inl _ (bops_add_id_add_ann_id_equals_ann S rS c timesS plusS (A_eqv_reflexive S rS eqvS))

|}. 


Definition bs_proofs_add_zero : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (plusS timesS : binary_op S), 
     eqv_proofs S rS -> 
     bs_proofs S rS plusS timesS -> 
        bs_proofs 
           (with_constant S) 
           (brel_add_constant S rS c)
           (bop_add_id S plusS c)
           (bop_add_ann S timesS c)
:= λ S rS c plusS timesS eqvS pS, 
{|
  A_bs_left_distributive_d    := 
     bops_add_zero_left_distributive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_bs_left_distributive_d S rS plusS timesS pS) 

; A_bs_right_distributive_d   := 
     bops_add_zero_right_distributive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_bs_right_distributive_d S rS plusS timesS pS) 

; A_bs_left_left_absorptive_d      := 
     bops_add_zero_left_left_absorptive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_bs_left_left_absorptive_d S rS plusS timesS pS)

; A_bs_left_right_absorptive_d      := 
     bops_add_zero_left_right_absorptive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_bs_left_right_absorptive_d S rS plusS timesS pS)

; A_bs_right_left_absorptive_d     := 
     bops_add_zero_right_left_absorptive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_bs_right_left_absorptive_d S rS plusS timesS pS)

; A_bs_right_right_absorptive_d     := 
     bops_add_zero_right_right_absorptive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_bs_right_right_absorptive_d S rS plusS timesS pS)

; A_bs_plus_id_is_times_ann_d := 
     inl _ (bops_add_id_add_ann_id_equals_ann S rS c plusS timesS (A_eqv_reflexive S rS eqvS))

; A_bs_times_id_is_plus_ann_d :=  
    bops_add_zero_ann_equals_id_decide S rS 
      (brel_get_witness S rS (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS)))
      c plusS timesS 
      (A_eqv_reflexive S rS eqvS)
      (A_bs_times_id_is_plus_ann_d S rS plusS timesS pS)
|}. 


Definition bs_proofs_product : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     bs_proofs S rS plusS timesS -> 
     bs_proofs T rT plusT timesT -> 
        bs_proofs (S * T) 
           (brel_product S T rS rT) 
           (bop_product S T plusS plusT)
           (bop_product S T timesS timesT)

:= λ S T rS rT plusS timesS plusT timesT eqvS eqvT pS pT, 
{|
  A_bs_left_distributive_d := 
     bop_product_left_distributive_decide S T rS rT plusS timesS plusT timesT 
        (A_eqv_nontrivial S rS eqvS)  
        (A_eqv_nontrivial T rT eqvT)  
        (A_bs_left_distributive_d S rS plusS timesS pS)
        (A_bs_left_distributive_d T rT plusT timesT pT)
; A_bs_right_distributive_d := 
     bop_product_right_distributive_decide S T rS rT plusS timesS plusT timesT 
        (A_eqv_nontrivial S rS eqvS)  
        (A_eqv_nontrivial T rT eqvT)  
        (A_bs_right_distributive_d S rS plusS timesS pS)
        (A_bs_right_distributive_d T rT plusT timesT pT)

; A_bs_left_left_absorptive_d := 
     bops_product_left_left_absorptive_decide S T 
        (brel_get_witness S rS (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS)))  
        (brel_get_witness T rT (brel_nontrivial_witness T rT (A_eqv_nontrivial T rT eqvT)))  
        rS rT plusS timesS plusT timesT 
        (A_bs_left_left_absorptive_d S rS plusS timesS pS)
        (A_bs_left_left_absorptive_d T rT plusT timesT pT)
; A_bs_left_right_absorptive_d := 
     bops_product_left_right_absorptive_decide S T 
        (brel_get_witness S rS (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS)))  
        (brel_get_witness T rT (brel_nontrivial_witness T rT (A_eqv_nontrivial T rT eqvT)))  
        rS rT plusS timesS plusT timesT 
        (A_bs_left_right_absorptive_d S rS plusS timesS pS)
        (A_bs_left_right_absorptive_d T rT plusT timesT pT)
; A_bs_right_left_absorptive_d := 
     bops_product_right_left_absorptive_decide S T 
        (brel_get_witness S rS (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS)))  
        (brel_get_witness T rT (brel_nontrivial_witness T rT (A_eqv_nontrivial T rT eqvT)))  
        rS rT plusS timesS plusT timesT 
        (A_bs_right_left_absorptive_d S rS plusS timesS pS)
        (A_bs_right_left_absorptive_d T rT plusT timesT pT)
; A_bs_right_right_absorptive_d := 
     bops_product_right_right_absorptive_decide S T 
        (brel_get_witness S rS (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS)))  
        (brel_get_witness T rT (brel_nontrivial_witness T rT (A_eqv_nontrivial T rT eqvT)))  
        rS rT plusS timesS plusT timesT 
        (A_bs_right_right_absorptive_d S rS plusS timesS pS)
        (A_bs_right_right_absorptive_d T rT plusT timesT pT)


; A_bs_plus_id_is_times_ann_d := 
     bop_product_id_equals_ann_decide S T rS rT plusS timesS plusT timesT 
        (A_bs_plus_id_is_times_ann_d S rS plusS timesS pS)
        (A_bs_plus_id_is_times_ann_d T rT plusT timesT pT)
; A_bs_times_id_is_plus_ann_d :=  
     bop_product_id_equals_ann_decide S T rS rT timesS plusS timesT plusT  
        (A_bs_times_id_is_plus_ann_d S rS plusS timesS pS)
        (A_bs_times_id_is_plus_ann_d T rT plusT timesT pT)

|}. 



Definition bs_proofs_llex : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 

     sg_CS_proofs S rS plusS ->          (*NB*) 
     sg_proofs S rS timesS ->            
     sg_C_proofs T rT plusT ->           (*NB*) 
     sg_proofs T rT timesT ->            

     bs_proofs S rS plusS timesS -> 
     bs_proofs T rT plusT timesT -> 

        bs_proofs (S * T) 
           (brel_product S T rS rT) 
           (bop_llex S T rS plusS plusT)
           (bop_product S T timesS timesT)

:= λ S T rS rT plusS timesS plusT timesT eqvS eqvT sg_CS_S sg_S sg_C_T sg_T pS pT, 
{|
  A_bs_left_distributive_d    := 
   bops_llex_product_left_distributive_decide S T 
     rS rT plusS timesS plusT timesT 
     (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS))
     (A_eqv_reflexive S rS eqvS) 
     (A_eqv_symmetric S rS eqvS) 
     (A_eqv_transitive S rS eqvS) 
     (A_sg_congruence S rS timesS sg_S) 
     (A_sg_CS_selective S rS plusS sg_CS_S)
     (A_sg_CS_commutative S rS plusS sg_CS_S)
     (A_eqv_nontrivial T rT eqvT)  
     (A_eqv_reflexive T rT eqvT) 
     (A_eqv_symmetric T rT eqvT) 
     (A_eqv_transitive T rT eqvT) 
     (A_sg_C_commutative T rT plusT sg_C_T)
     (A_sg_left_cancel_d S rS timesS  sg_S) 
     (A_sg_left_constant_d T rT timesT sg_T)
     (A_bs_left_distributive_d S rS plusS timesS pS)
     (A_bs_left_distributive_d T rT plusT timesT pT)
; A_bs_right_distributive_d   := 
   bops_llex_product_right_distributive_decide S T 
     rS rT plusS timesS plusT timesT 
     (brel_nontrivial_witness S rS (A_eqv_nontrivial S rS eqvS))
     (A_eqv_reflexive S rS eqvS) 
     (A_eqv_symmetric S rS eqvS) 
     (A_eqv_transitive S rS eqvS) 
     (A_sg_congruence S rS timesS sg_S) 
     (A_sg_CS_selective S rS plusS sg_CS_S)
     (A_sg_CS_commutative S rS plusS sg_CS_S)
     (A_eqv_nontrivial T rT eqvT)  
     (A_eqv_reflexive T rT eqvT) 
     (A_eqv_symmetric T rT eqvT) 
     (A_eqv_transitive T rT eqvT) 
     (A_sg_C_commutative T rT plusT sg_C_T)
     (A_sg_right_cancel_d S rS timesS  sg_S) 
     (A_sg_right_constant_d T rT timesT sg_T)
     (A_bs_right_distributive_d S rS plusS timesS pS)
     (A_bs_right_distributive_d T rT plusT timesT pT)

; A_bs_plus_id_is_times_ann_d :=  
   bops_llex_product_id_equals_ann_decide S T 
   rS rT plusS timesS plusT timesT 
   (A_eqv_reflexive S rS eqvS)  
   (A_eqv_symmetric S rS eqvS)  
   (A_eqv_transitive S rS eqvS)  
   (A_sg_CS_commutative S rS plusS sg_CS_S)
   (A_eqv_reflexive T rT eqvT)  
   (A_eqv_symmetric T rT eqvT)  
   (A_eqv_transitive T rT eqvT)  
   (A_bs_plus_id_is_times_ann_d S rS plusS timesS pS)
   (A_bs_plus_id_is_times_ann_d T rT plusT timesT pT)

; A_bs_times_id_is_plus_ann_d :=  
   bops_product_llex_id_equals_ann_decide S T 
   rS rT plusS timesS plusT timesT 
   (A_eqv_reflexive S rS eqvS)  
   (A_eqv_symmetric S rS eqvS)  
   (A_eqv_transitive S rS eqvS)  
   (A_sg_CS_commutative S rS plusS sg_CS_S)
   (A_eqv_reflexive T rT eqvT)  
   (A_eqv_symmetric T rT eqvT)  
   (A_eqv_transitive T rT eqvT)  
   (A_bs_times_id_is_plus_ann_d S rS plusS timesS pS)
   (A_bs_times_id_is_plus_ann_d T rT plusT timesT pT)


; A_bs_left_left_absorptive_d      := 
    bops_llex_product_left_left_absorptive_decide S T 
       (brel_get_witness T rT (brel_nontrivial_witness T rT (A_eqv_nontrivial T rT eqvT)))  
        rS rT plusS timesS plusT timesT 
    (A_eqv_symmetric S rS eqvS) 
    (A_eqv_transitive S rS eqvS) 
    (A_eqv_reflexive T rT eqvT) 
    (A_bs_left_left_absorptive_d S rS plusS timesS pS)
    (A_bs_left_left_absorptive_d T rT plusT timesT pT)
    (A_sg_anti_left_d S rS timesS sg_S)


; A_bs_left_right_absorptive_d      := 
    bops_llex_product_left_right_absorptive_decide S T 
       (brel_get_witness T rT (brel_nontrivial_witness T rT (A_eqv_nontrivial T rT eqvT)))  
        rS rT plusS timesS plusT timesT 
    (A_eqv_symmetric S rS eqvS) 
    (A_eqv_transitive S rS eqvS) 
    (A_eqv_reflexive T rT eqvT) 
    (A_bs_left_right_absorptive_d S rS plusS timesS pS)
    (A_bs_left_right_absorptive_d T rT plusT timesT pT)
    (A_sg_anti_right_d S rS timesS sg_S)


; A_bs_right_left_absorptive_d      := 
    bops_llex_product_right_left_absorptive_decide S T 
       (brel_get_witness T rT (brel_nontrivial_witness T rT (A_eqv_nontrivial T rT eqvT)))  
        rS rT plusS timesS plusT timesT 
    (A_eqv_symmetric S rS eqvS) 
    (A_eqv_transitive S rS eqvS) 
    (A_eqv_reflexive T rT eqvT) 
    (A_bs_right_left_absorptive_d S rS plusS timesS pS)
    (A_bs_right_left_absorptive_d T rT plusT timesT pT)
    (A_sg_anti_left_d S rS timesS sg_S)

; A_bs_right_right_absorptive_d      := 
    bops_llex_product_right_right_absorptive_decide S T 
       (brel_get_witness T rT (brel_nontrivial_witness T rT (A_eqv_nontrivial T rT eqvT)))  
        rS rT plusS timesS plusT timesT 
    (A_eqv_symmetric S rS eqvS) 
    (A_eqv_transitive S rS eqvS) 
    (A_eqv_reflexive T rT eqvT) 
    (A_bs_right_right_absorptive_d S rS plusS timesS pS)
    (A_bs_right_right_absorptive_d T rT plusT timesT pT)
    (A_sg_anti_right_d S rS timesS sg_S)

|}. 








