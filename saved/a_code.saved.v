


(* order *) 

Definition po_proofs_llte : 
   ∀ (S : Type) 
     (r : brel S) 
     (b : binary_op S), 
     eqv_proofs S r -> 
     sg_CI_proofs S r b -> 
          po_proofs S r (brel_llte S r b) 
:= λ S r b eqvS sgS, 
{|
(*
  A_po_nontrivial   := brel_llte_nontrivial S r b 
                          (A_eqv_symmetric S r eqvS) 
                          (A_sg_CI_not_is_left S r b sgS)
                          (bop_idempotent_implies_somewhere_left S r b 
                             (brel_nontrivial_not_false S r (A_eqv_nontrivial S r eqvS))
                             (A_sg_CI_idempotent S r b sgS) 
                          ) 
*) 
  A_po_congruence    := brel_llte_congruence S r r b 
                          (A_eqv_congruence S r eqvS) 
                          (A_sg_CI_congruence S r b sgS) 
; A_po_reflexive     := brel_llte_reflexive S r b 
                          (A_eqv_symmetric S r eqvS) 
                          (A_sg_CI_idempotent S r b sgS) 
                          (A_eqv_reflexive S r eqvS) 
; A_po_transitive    := brel_llte_transitive S r b 
                          (A_eqv_reflexive S r eqvS) 
                          (A_eqv_symmetric S r eqvS) 
                          (A_sg_CI_associative S r b sgS) 
                          (A_sg_CI_congruence S r b sgS) 
                          (A_eqv_transitive S r eqvS) 
; A_po_antisymmetric := brel_llte_antisymmetric S r b 
                          (A_eqv_symmetric S r eqvS) 
                          (A_eqv_transitive S r eqvS) 
                          (A_sg_CI_commutative S r b sgS) 
; A_po_total_d       := brel_llte_total_decide S r b 
                          (A_eqv_symmetric S r eqvS) 
                          (A_eqv_transitive S r eqvS) 
                          (A_sg_CI_commutative S r b sgS) 
                          (A_sg_CI_selective_d S r b sgS) 
|}. 


Definition po_proofs_product : 
   ∀ (S T : Type) 
     (eqS : brel S) 
     (eqT : brel T) 
     (rS :  brel S) 
     (rT :  brel T), 
      eqv_proofs S eqS ->  
      eqv_proofs T eqT ->  
      po_proofs S eqS rS ->  
      po_proofs T eqT rT -> 
         po_proofs (S * T) (brel_product S T eqS eqT) (brel_product S T rS rT)
:= λ S T eqS eqT rS rT eqvS eqvT poS poT, 
{|
 A_po_congruence    := brel_product_congruence S T eqS eqT rS rT
                           (A_po_congruence S eqS rS poS) 
                           (A_po_congruence T eqT rT poT) 
; A_po_reflexive     := brel_product_reflexive S T rS rT 
                           (A_po_reflexive S eqS rS poS) 
                           (A_po_reflexive T eqT rT poT)
; A_po_transitive    := brel_product_transitive S T rS rT 
                           (A_po_transitive S eqS rS poS) 
                           (A_po_transitive T eqT rT poT)
; A_po_antisymmetric := brel_product_antisymmetric S T eqS eqT rS rT
                           (A_po_antisymmetric S eqS rS poS) 
                           (A_po_antisymmetric T eqT rT poT) 
; A_po_total_d       := brel_product_total_decide_v2 S T eqS eqT rS rT
                           (A_eqv_nontrivial S eqS eqvS)
                           (A_eqv_nontrivial T eqT eqvT)
                           (A_po_antisymmetric S eqS rS poS) 
                           (A_po_antisymmetric T eqT rT poT) 
                           (A_po_total_d  S eqS rS poS) 
                           (A_po_total_d  T eqT rT poT)
|}. 

(* bsg *) 

Definition sg_sg_proofs_min_plus : sg_sg_proofs nat brel_eq_nat bop_min bop_plus := 
{|
  A_sg_sg_left_distributive_d    := inl _ bop_min_plus_left_distributive
; A_sg_sg_right_distributive_d   := inl _ bop_min_plus_right_distributive
; A_sg_sg_plus_id_is_times_ann_d := inr _ bop_min_plus_not_id_equals_ann
; A_sg_sg_times_id_is_plus_ann_d := inl _ bop_plus_min_id_equals_ann
|}. 


(* 

Definition sg_sg_BD_proofs_union_intersect :    ∀ (S : Type) (r : brel S) (c : cas_constant), 
      eqv_proofs S r ->     
      sg_sg_BD_proofs (with_constant (finite_set S)) 
         (brel_add_constant (finite_set S) (brel_set S r) c) 
         (bop_add_ann (finite_set S) (bop_union S r) c) 
         (bop_add_id (finite_set S) (bop_intersect  S r) c) 
:= λ S r c eqvS,
let congS := A_eqv_congruence S r eqvS in 
let refS := A_eqv_reflexive S r eqvS in 
let symS := A_eqv_symmetric S r eqvS in 
let transS := A_eqv_transitive S r eqvS in 
{|
  A_sg_sg_BD_left_distributive      := bops_add_ann_add_id_left_distributive (finite_set S) 
                                            (brel_set S r) c 
                                            (bop_union S r) 
                                            (bop_intersect S r) 
                                            (brel_set_congruence S r refS symS transS)
                                            (brel_set_reflexive S r refS symS transS)
                                            (brel_set_symmetric S r symS)
                                            (bop_union_idempotent S r refS symS transS)
                                            (bop_union_commutative S r refS symS transS)
                                            (union_intersect_left_absorptive
                                              S r refS symS transS)
                                            (bop_union_intersect_left_distributive 
                                              S r refS symS transS)
; A_sg_sg_BD_right_distributive    := bops_add_ann_add_id_right_distributive (finite_set S) 
                                            (brel_set S r) c 
                                            (bop_union S r) 
                                            (bop_intersect S r) 
                                            (brel_set_congruence S r refS symS transS)
                                            (brel_set_reflexive S r refS symS transS)
                                            (brel_set_symmetric S r symS)
                                            (bop_union_idempotent S r refS symS transS)
                                            (bop_union_commutative S r refS symS transS)
                                            (union_intersect_right_absorptive
                                              S r refS symS transS)
                                            (bop_union_intersect_right_distributive 
                                              S r refS symS transS)
; A_sg_sg_BD_plus_id_is_times_ann := bops_add_ann_add_id_id_equals_ann (finite_set S)  
                                            (brel_set S r) c 
                                            (bop_union S r) 
                                            (bop_intersect S r) 
                                            (brel_set_reflexive S r refS symS transS)
                                            (intersect_union_id_equals_ann 
                                              S r refS symS transS)
; A_sg_sg_BD_times_id_is_plus_ann := bops_id_equals_ann_same_constant (finite_set S)  
                                            (brel_set S r) c 
                                            (bop_intersect S r) 
                                            (bop_union S r) 
                                            (brel_set_reflexive S r refS symS transS)
|}. 


Definition sg_sg_BD_proofs_intersect_union :    ∀ (S : Type) (r : brel S) (c : cas_constant), 
      eqv_proofs S r ->     
      sg_sg_BD_proofs (with_constant (finite_set S)) 
         (brel_add_constant (finite_set S) (brel_set S r) c) 
         (bop_add_id (finite_set S) (bop_intersect  S r) c) 
         (bop_add_ann (finite_set S) (bop_union S r) c) 
:= λ S r c eqvS,
let congS := A_eqv_congruence S r eqvS in 
let refS := A_eqv_reflexive S r eqvS in 
let symS := A_eqv_symmetric S r eqvS in 
let transS := A_eqv_transitive S r eqvS in 
{|
  A_sg_sg_BD_left_distributive      := bop_add_id_add_ann_left_distributive (finite_set S) 
                                            (brel_set S r) c 
                                            (bop_intersect S r) 
                                            (bop_union S r) 
                                            (brel_set_reflexive S r refS symS transS)
                                            (bop_intersect_union_left_distributive 
                                              S r refS symS transS)
; A_sg_sg_BD_right_distributive    :=  bop_add_id_add_ann_right_distributive (finite_set S) 
                                            (brel_set S r) c 
                                            (bop_intersect S r) 
                                            (bop_union S r) 
                                            (brel_set_reflexive S r refS symS transS)
                                            (bop_intersect_union_right_distributive 
                                              S r refS symS transS)
; A_sg_sg_BD_plus_id_is_times_ann := bops_id_equals_ann_same_constant (finite_set S)  
                                            (brel_set S r) c 
                                            (bop_intersect S r) 
                                            (bop_union S r) 
                                            (brel_set_reflexive S r refS symS transS)
; A_sg_sg_BD_times_id_is_plus_ann := bops_add_ann_add_id_id_equals_ann (finite_set S)  
                                            (brel_set S r) c 
                                            (bop_union S r) 
                                            (bop_intersect S r) 
                                            (brel_set_reflexive S r refS symS transS)
                                            (intersect_union_id_equals_ann 
                                              S r refS symS transS)
|}. 



*) 


Definition sg_sg_D_proofs_product : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_sg_D_proofs S rS plusS timesS -> 
     sg_sg_D_proofs T rT plusT timesT -> 
        sg_sg_D_proofs (S * T) 
           (brel_product S T rS rT) 
           (bop_product S T plusS plusT)
           (bop_product S T timesS timesT)
:= λ S T rS rT plusS timesS plusT timesT eqvS eqvT pS pT, 
{|
  A_sg_sg_D_left_distributive     := bop_product_left_distributive S T 
                                     rS rT plusS timesS plusT timesT 
                                     (A_sg_sg_D_left_distributive S rS plusS timesS pS)
                                     (A_sg_sg_D_left_distributive T rT plusT timesT pT)
; A_sg_sg_D_right_distributive   := bop_product_right_distributive S T 
                                     rS rT plusS timesS plusT timesT 
                                     (A_sg_sg_D_right_distributive S rS plusS timesS pS)
                                     (A_sg_sg_D_right_distributive T rT plusT timesT pT)
; A_sg_sg_D_plus_id_is_times_ann_d :=  bop_product_id_equals_ann_decide S T 
                                     rS rT plusS timesS plusT timesT 
                                     (A_eqv_symmetric S rS eqvS)  
                                     (A_eqv_transitive S rS eqvS)  
                                     (A_eqv_symmetric T rT eqvT)  
                                     (A_eqv_transitive T rT eqvT)  
                                     (A_sg_sg_D_plus_id_is_times_ann_d S rS plusS timesS pS)
                                     (A_sg_sg_D_plus_id_is_times_ann_d T rT plusT timesT pT)
; A_sg_sg_D_times_id_is_plus_ann_d :=  bop_product_id_equals_ann_decide S T 
                                     rS rT timesS plusS timesT plusT  
                                     (A_eqv_symmetric S rS eqvS)  
                                     (A_eqv_transitive S rS eqvS)  
                                     (A_eqv_symmetric T rT eqvT)  
                                     (A_eqv_transitive T rT eqvT)  
                                     (A_sg_sg_D_times_id_is_plus_ann_d S rS plusS timesS pS)
                                     (A_sg_sg_D_times_id_is_plus_ann_d T rT plusT timesT pT)
|}. 



Definition sg_sg_BD_proofs_product : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_sg_BD_proofs S rS plusS timesS -> 
     sg_sg_BD_proofs T rT plusT timesT -> 
        sg_sg_BD_proofs (S * T) 
           (brel_product S T rS rT) 
           (bop_product S T plusS plusT)
           (bop_product S T timesS timesT)
:= λ S T rS rT plusS timesS plusT timesT eqvS eqvT sg_sg_BDS sg_sg_BDT, 
{|
  A_sg_sg_BD_left_distributive     := bop_product_left_distributive S T 
                                     rS rT plusS timesS plusT timesT 
                                     (A_sg_sg_BD_left_distributive S rS plusS timesS sg_sg_BDS)
                                     (A_sg_sg_BD_left_distributive T rT plusT timesT sg_sg_BDT)
; A_sg_sg_BD_right_distributive   := bop_product_right_distributive S T 
                                     rS rT plusS timesS plusT timesT 
                                     (A_sg_sg_BD_right_distributive S rS plusS timesS sg_sg_BDS)
                                     (A_sg_sg_BD_right_distributive T rT plusT timesT sg_sg_BDT)
; A_sg_sg_BD_plus_id_is_times_ann :=  bop_product_id_equals_ann S T 
                                     rS rT plusS timesS plusT timesT 
                                     (A_eqv_symmetric S rS eqvS)  
                                     (A_eqv_transitive S rS eqvS)  
                                     (A_eqv_symmetric T rT eqvT)  
                                     (A_eqv_transitive T rT eqvT)  
                                     (A_sg_sg_BD_plus_id_is_times_ann S rS plusS timesS sg_sg_BDS)
                                     (A_sg_sg_BD_plus_id_is_times_ann T rT plusT timesT sg_sg_BDT)
; A_sg_sg_BD_times_id_is_plus_ann  :=  bop_product_id_equals_ann S T 
                                     rS rT timesS plusS timesT plusT  
                                     (A_eqv_symmetric S rS eqvS)  
                                     (A_eqv_transitive S rS eqvS)  
                                     (A_eqv_symmetric T rT eqvT)  
                                     (A_eqv_transitive T rT eqvT)  
                                     (A_sg_sg_BD_times_id_is_plus_ann S rS plusS timesS sg_sg_BDS)
                                     (A_sg_sg_BD_times_id_is_plus_ann T rT plusT timesT sg_sg_BDT)
|}. 



(*  Definition sg_sg_proofs_llex_product : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     sg_proofs S rS timesS -> 
     sg_proofs T rT timesT -> 
     sg_CS_sg_proofs S rS plusS timesS -> 
     sg_sg_proofs T rT plusT timesT -> 
        sg_sg_proofs (S * T) 
           (brel_product S T rS rT) 
           (bop_llex S T rS plusS plusT)
           (bop_product S T timesS timesT)

:= λ S T rS rT plusS timesS plusT timesT eqvS eqvT sgS sgT pS pT, 
{|
  A_sg_sg_left_distributive_d    := bop_llex_product_left_distributive_decide S T 
                                     rS rT plusS timesS plusT timesT 
                                     (A_eqv_reflexive S rS eqvS)  
                                     (A_eqv_symmetric S rS eqvS)  
                                     (A_eqv_transitive S rS eqvS)  
                                     (A_eqv_nontrivial T rT eqvT)  
                                     (A_eqv_reflexive T rT eqvT)  
                                     (A_eqv_transitive T rT eqvT) 
                                     (A_sg_congruence S rS timesS  sgT)
                                     (A_sg_sg_left_distributive_d S rS plusS timesS pS)
                                     (A_sg_sg_left_distributive_d T rT plusT timesT pT)
                                     (a_sg_left_cancel_d S rS timesS sgS)
                                     (a_sg_left_constant_d T rT timesT sgT)
; A_sg_sg_right_distributive_d   :=  bop_llex_product_right_distributive_decide S T 
                                     rS rT plusS timesS plusT timesT 
                                     (A_eqv_reflexive S rS eqvS)  
                                     (A_eqv_symmetric S rS eqvS)  
                                     (A_eqv_transitive S rS eqvS)  
                                     (A_eqv_nontrivial T rT eqvT)  
                                     (A_eqv_reflexive T rT eqvT)  
                                     (A_eqv_transitive T rT eqvT) 
                                     (A_sg_congruence S rS timesS  sgT)
                                     (A_sg_sg_right_distributive_d S rS plusS timesS pS)
                                     (A_sg_sg_left_distributive_d T rT plusT timesT pT)
                                     (a_sg_right_cancel_d S rS timesS sgS)
                                     (a_sg_left_constant_d T rT timesT sgT)
; A_sg_sg_plus_id_is_times_ann_d :=  bop_llex_product_id_equals_ann_decide S T 
                                     rS rT plusS timesS plusT timesT 
 
                                     (A_eqv_symmetric S rS eqvS)  
                                     (A_eqv_transitive S rS eqvS)  
                                     (A_eqv_symmetric T rT eqvT)  
                                     (A_eqv_transitive T rT eqvT)  
                                     (A_sg_sg_plus_id_is_times_ann_d S rS plusS timesS pS)
                                     (A_sg_sg_plus_id_is_times_ann_d T rT plusT timesT pT)
; A_sg_sg_times_id_is_plus_ann_d :=  bop_llex_product_id_equals_ann_decide S T 
                                     rS rT timesS plusS timesT plusT  
                                     (A_eqv_symmetric S rS eqvS)  
                                     (A_eqv_transitive S rS eqvS)  
                                     (A_eqv_symmetric T rT eqvT)  
                                     (A_eqv_transitive T rT eqvT)  
                                     (A_sg_sg_times_id_is_plus_ann_d S rS plusS timesS pS)
                                     (A_sg_sg_times_id_is_plus_ann_d T rT plusT timesT pT)
|}. 
*) 

(* 
Definition A_sg_CS_sg_product : ∀ (S T : Type),  A_sg_CS_sg S -> A_sg_CS_sg T -> A_sg_CS_sg (S * T) 
:= λ S T sg_sgS sg_sgT, 
   {| 
     A_sg_CS_sg_eq        := brel_product S T 
                           (A_sg_sg_eq S sg_sgS) 
                           (A_sg_sg_eq T sg_sgT) 
   ; A_sg_CS_sg_plus       := bop_product S T 
                           (A_sg_sg_plus S sg_sgS) 
                           (A_sg_sg_plus T sg_sgT) 
   ; A_sg_CS_sg_times       := bop_product S T 
                           (A_sg_sg_times S sg_sgS) 
                           (A_sg_sg_times T sg_sgT) 
   ; A_sg_CS_sg_eqv_proofs := eqv_proofs_product S T 
                           (A_sg_sg_eq S sg_sgS) 
                           (A_sg_sg_eq T sg_sgT) 
                           (A_sg_sg_eqv_proofs S sg_sgS) 
                           (A_sg_sg_eqv_proofs T sg_sgT) 
   ; A_sg_CS_sg_plus_proofs := sg_proofs_product S T 
                           (A_sg_sg_eq S sg_sgS) 
                           (A_sg_sg_eq T sg_sgT) 
                           (A_sg_sg_plus S sg_sgS) 
                           (A_sg_sg_plus T sg_sgT) 
                           (A_sg_sg_eqv_proofs S sg_sgS) 
                           (A_sg_sg_eqv_proofs T sg_sgT) 
                           (A_sg_sg_plus_proofs S sg_sgS) 
                           (A_sg_sg_plus_proofs T sg_sgT) 
   ; A_sg_CS_sg_times_proofs := sg_proofs_product S T 
                           (A_sg_sg_eq S sg_sgS) 
                           (A_sg_sg_eq T sg_sgT) 
                           (A_sg_sg_times S sg_sgS) 
                           (A_sg_sg_times T sg_sgT) 
                           (A_sg_sg_eqv_proofs S sg_sgS) 
                           (A_sg_sg_eqv_proofs T sg_sgT) 
                           (A_sg_sg_times_proofs S sg_sgS) 
                           (A_sg_sg_times_proofs T sg_sgT) 
   ; A_sg_CS_sg_proofs    := sg_sg_proofs_product S T 
                           (A_sg_sg_eq S sg_sgS) 
                           (A_sg_sg_eq T sg_sgT) 
                           (A_sg_sg_plus S sg_sgS) 
                           (A_sg_sg_times S sg_sgS) 
                           (A_sg_sg_plus T sg_sgT) 
                           (A_sg_sg_times T sg_sgT) 
                           (A_sg_sg_eqv_proofs S sg_sgS) 
                           (A_sg_sg_eqv_proofs T sg_sgT) 
                           (A_sg_sg_proofs S sg_sgS) 
                           (A_sg_sg_proofs T sg_sgT) 
   ; A_sg_CS_sg_ast     := Ast_sg_CS_sg_product(A_sg_sg_ast S sg_sgS, A_sg_sg_ast T sg_sgT)
   |}. 














Definition A_sr_product : ∀ (S T : Type),  A_sr S -> A_sr T -> A_sr (S * T) 
:= λ S T srS srT, 
   {| 
     A_sr_eq        := brel_product S T 
                           (A_sr_eq S srS) 
                           (A_sr_eq T srT) 
   ; A_sr_plus       := bop_product S T 
                           (A_sr_plus S srS) 
                           (A_sr_plus T srT) 
   ; A_sr_times       := bop_product S T 
                           (A_sr_times S srS) 
                           (A_sr_times T srT) 
   ; A_sr_eqv_proofs := eqv_proofs_product S T 
                           (A_sr_eq S srS) 
                           (A_sr_eq T srT) 
                           (A_sr_eqv_proofs S srS) 
                           (A_sr_eqv_proofs T srT) 
   ; A_sr_plus_proofs := csg_proofs_product S T 
                           (A_sr_eq S srS) 
                           (A_sr_eq T srT) 
                           (A_sr_plus S srS) 
                           (A_sr_plus T srT) 
                           (A_sr_eqv_proofs S srS) 
                           (A_sr_eqv_proofs T srT) 
                           (A_sr_plus_proofs S srS) 
                           (A_sr_plus_proofs T srT) 
   ; A_sr_times_proofs := sg_proofs_product S T 
                           (A_sr_eq S srS) 
                           (A_sr_eq T srT) 
                           (A_sr_times S srS) 
                           (A_sr_times T srT) 
                           (A_sr_eqv_proofs S srS) 
                           (A_sr_eqv_proofs T srT) 
                           (A_sr_times_proofs S srS) 
                           (A_sr_times_proofs T srT) 
   ; A_sr_sr_proofs := sr_proofs_product S T 
                           (A_sr_eq S srS) 
                           (A_sr_eq T srT) 
                           (A_sr_plus S srS) 
                           (A_sr_times S srS) 
                           (A_sr_plus T srT) 
                           (A_sr_times T srT) 
                           (A_sr_eqv_proofs S srS) 
                           (A_sr_eqv_proofs T srT) 
                           (A_sr_sr_proofs S srS) 
                           (A_sr_sr_proofs T srT) 
   ; A_sr_ast        := Ast_sg_sg_product (A_sr_ast S srS, A_sr_ast T srT)
   |}. 

(* csr *) 

Definition A_csr_product : ∀ (S T : Type),  A_csr S -> A_csr T -> A_csr (S * T) 
:= λ S T csrS csrT, 
   {| 
     A_csr_eq        := brel_product S T 
                           (A_csr_eq S csrS) 
                           (A_csr_eq T csrT) 
   ; A_csr_plus       := bop_product S T 
                           (A_csr_plus S csrS) 
                           (A_csr_plus T csrT) 
   ; A_csr_times       := bop_product S T 
                           (A_csr_times S csrS) 
                           (A_csr_times T csrT) 
   ; A_csr_eqv_proofs := eqv_proofs_product S T 
                           (A_csr_eq S csrS) 
                           (A_csr_eq T csrT) 
                           (A_csr_eqv_proofs S csrS) 
                           (A_csr_eqv_proofs T csrT) 
   ; A_csr_plus_proofs := csg_proofs_product S T 
                           (A_csr_eq S csrS) 
                           (A_csr_eq T csrT) 
                           (A_csr_plus S csrS) 
                           (A_csr_plus T csrT) 
                           (A_csr_eqv_proofs S csrS) 
                           (A_csr_eqv_proofs T csrT) 
                           (A_csr_plus_proofs S csrS) 
                           (A_csr_plus_proofs T csrT) 
   ; A_csr_times_proofs := sg_proofs_product S T 
                           (A_csr_eq S csrS) 
                           (A_csr_eq T csrT) 
                           (A_csr_times S csrS) 
                           (A_csr_times T csrT) 
                           (A_csr_eqv_proofs S csrS) 
                           (A_csr_eqv_proofs T csrT) 
                           (A_csr_times_proofs S csrS) 
                           (A_csr_times_proofs T csrT) 
   ; A_csr_csr_proofs := csr_proofs_product S T 
                           (A_csr_eq S csrS) 
                           (A_csr_eq T csrT) 
                           (A_csr_plus S csrS) 
                           (A_csr_times S csrS) 
                           (A_csr_plus T csrT) 
                           (A_csr_times T csrT) 
                           (A_csr_eqv_proofs S csrS) 
                           (A_csr_eqv_proofs T csrT) 
                           (A_csr_csr_proofs S csrS) 
                           (A_csr_csr_proofs T csrT) 
   ; A_csr_ast        := CSR_product(A_csr_ast S csrS, A_csr_ast T csrT)
   |}. 


(* pa *) 

Definition A_pa_product : ∀ (S T : Type),  A_pa S -> A_pa T -> A_pa (S * T) 
:= λ S T paS paT, 
   {| 
     A_pa_eq        := brel_product S T 
                           (A_pa_eq S paS) 
                           (A_pa_eq T paT) 
   ; A_pa_plus       := bop_product S T 
                           (A_pa_plus S paS) 
                           (A_pa_plus T paT) 
   ; A_pa_times       := bop_product S T 
                           (A_pa_times S paS) 
                           (A_pa_times T paT) 
   ; A_pa_eqv_proofs := eqv_proofs_product S T 
                           (A_pa_eq S paS) 
                           (A_pa_eq T paT) 
                           (A_pa_eqv_proofs S paS) 
                           (A_pa_eqv_proofs T paT) 
   ; A_pa_plus_proofs := sg_CI_proofs_product S T 
                           (A_pa_eq S paS) 
                           (A_pa_eq T paT) 
                           (A_pa_plus S paS) 
                           (A_pa_plus T paT) 
                           (A_pa_eqv_proofs S paS) 
                           (A_pa_eqv_proofs T paT) 
                           (A_pa_plus_proofs S paS) 
                           (A_pa_plus_proofs T paT) 
   ; A_pa_times_proofs := sg_proofs_product S T 
                           (A_pa_eq S paS) 
                           (A_pa_eq T paT) 
                           (A_pa_times S paS) 
                           (A_pa_times T paT) 
                           (A_pa_eqv_proofs S paS) 
                           (A_pa_eqv_proofs T paT) 
                           (A_pa_times_proofs S paS) 
                           (A_pa_times_proofs T paT) 
   ; A_pa_pa_proofs := csr_proofs_product S T 
                           (A_pa_eq S paS) 
                           (A_pa_eq T paT) 
                           (A_pa_plus S paS) 
                           (A_pa_times S paS) 
                           (A_pa_plus T paT) 
                           (A_pa_times T paT) 
                           (A_pa_eqv_proofs S paS) 
                           (A_pa_eqv_proofs T paT) 
                           (A_pa_pa_proofs S paS) 
                           (A_pa_pa_proofs T paT) 
   ; A_pa_ast        := PA_product(A_pa_ast S paS, A_pa_ast T paT)
   |}. 






Definition A_sg_sg_min_plus : A_sg_sg nat := 
   {| 
     A_sg_sg_eq           := brel_eq_nat 
   ; A_sg_sg_plus         := bop_min 
   ; A_sg_sg_times        := bop_plus 
   ; A_sg_sg_eqv_proofs   := eqv_proofs_eq_nat 
   ; A_sg_sg_plus_proofs  := A_sg_proofs_from_sg_CS_proofs _ _ _ sg_CS_proofs_min
   ; A_sg_sg_times_proofs := A_sg_proofs_from_sg_CK_proofs _ _ _ sg_CK_proofs_plus   
   ; A_sg_sg_proofs       := sg_sg_proofs_min_plus
   ; A_sg_sg_ast          := Ast_sg_sg_min_plus
   |}. 

*)

(* 
Definition A_pa_union_intersect : ∀ (S : Type) (c : cas_constant), A_eqv S -> A_pa (with_constant (finite_set S)) 
:= λ S c eqvS, 
   {| 
     A_pa_eq           := brel_add_constant (finite_set S) (brel_set S (A_eqv_eq S eqvS)) c  
   ; A_pa_plus         := bop_add_ann (finite_set S) (bop_union S (A_eqv_eq S eqvS)) c 
   ; A_pa_times        := bop_add_id (finite_set S) (bop_intersect S (A_eqv_eq S eqvS)) c 
   ; A_pa_eqv_proofs   := eqv_proofs_add_constant (finite_set S) (brel_set S (A_eqv_eq S eqvS)) c  
                              (eqv_proofs_brel_set S (A_eqv_eq S eqvS) (A_eqv_proofsS eqvS))
   ; A_pa_plus_proofs  := sg_CI_proofs_union_with_ann S (A_eqv_eq S eqvS) c (A_eqv_proofsS eqvS)
   ; A_pa_times_proofs := sg_proofs_from_sg_CI_proofs _ _ _ (sg_CI_proofs_intersect_with_id S (A_eqv_eq S eqvS) c (A_eqv_proofsS eqvS))
   ; A_pa_pa_proofs   := csr_proofs_union_intersect S (A_eqv_eq S eqvS) c (A_eqv_proofsS eqvS)
   ; A_pa_ast        := PA_union_intersect (c, A_eqv_ast S eqvS)
   |}. 


Definition A_pa_intersect_union : ∀ (S : Type) (c : cas_constant),  A_eqv S -> A_pa (with_constant (finite_set S)) 
:= λ S c eqvS, 
   {| 
     A_pa_eq           := brel_add_constant (finite_set S) (brel_set S (A_eqv_eq S eqvS)) c  
   ; A_pa_plus         := bop_add_id (finite_set S) (bop_intersect S (A_eqv_eq S eqvS)) c 
   ; A_pa_times        := bop_add_ann (finite_set S) (bop_union S (A_eqv_eq S eqvS)) c 
   ; A_pa_eqv_proofs   := eqv_proofs_add_constant (finite_set S) (brel_set S (A_eqv_eq S eqvS)) c  
                              (eqv_proofs_brel_set S (A_eqv_eq S eqvS) (A_eqv_proofsS eqvS))
   ; A_pa_plus_proofs  := sg_CI_proofs_intersect_with_id S (A_eqv_eq S eqvS) c (A_eqv_proofsS eqvS)
   ; A_pa_times_proofs := sg_proofs_from_sg_CI_proofs _ _ _ (sg_CI_proofs_union_with_ann S (A_eqv_eq S eqvS) c (A_eqv_proofsS eqvS))
   ; A_pa_pa_proofs   := csr_proofs_intersect_union S (A_eqv_eq S eqvS) c (A_eqv_proofsS eqvS)
   ; A_pa_ast        := PA_intersect_union (c, A_eqv_ast S eqvS)
   |}. 

*) 

(* order *) 


(* 

Definition A_po_llte_from_sg_CI : ∀ (S : Type),  A_sg_CI S -> A_po S 
:= λ S sg_CIS , 
   {| 
     A_po_eq         := A_sg_CI_eq S sg_CIS
   ; A_po_lte        := brel_llte S (A_sg_CI_eq S sg_CIS) (A_sg_CI_bop S sg_CIS) 
   ; A_po_eqv_proofs := A_sg_CI_eqv_proofs S sg_CIS
   ; A_po_po_proofs  := po_proofs_llte S 
                           (A_sg_CI_eq S sg_CIS) 
                           (A_sg_CI_bop S sg_CIS) 
                           (A_sg_CI_eqv_proofs S sg_CIS) 
                           (A_sg_CI_proofs S sg_CIS) 
   ; A_po_ast        := Ast_po_llte_from_sg_CI (A_sg_CI_ast S sg_CIS) 
   |}. 

(* 
Definition A_lte_nat := A_po_llte_from_sg_CI nat A_sg_CI_min. 
Definition A_gte_nat := A_po_llte_from_sg_CI nat A_sg_CI_max. 
*) 

Definition A_po_product : ∀ (S T : Type),  A_po S  -> A_po T -> A_po (S * T) 
:= λ S T poS poT, 
   {| 
     A_po_eq         := brel_product S T (A_po_eq S poS) (A_po_eq T poT)
   ; A_po_lte        := brel_product S T (A_po_lte S poS) (A_po_lte T poT)
   ; A_po_eqv_proofs := eqv_proofs_product S T 
                           (A_po_eq S poS) 
                           (A_po_eq T poT) 
                           (A_po_eqv_proofs S poS) 
                           (A_po_eqv_proofs T poT) 
   ; A_po_po_proofs  := po_proofs_product S T
                           (A_po_eq S poS) 
                           (A_po_eq T poT) 
                           (A_po_lte S poS) 
                           (A_po_lte T poT)          
                           (A_po_eqv_proofs S poS) 
                           (A_po_eqv_proofs T poT)                  
                           (A_po_po_proofs S poS) 
                           (A_po_po_proofs T poT) 
   ; A_po_ast        := PO_product(A_po_ast S poS, A_po_ast T poT)
   |}. 

*) 
