Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.

Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.a_code.proof_records.
Require Import CAS.a_code.a_cas_records.

Require Import CAS.a_code.a_cas.eqv.product. 
Require Import CAS.a_code.a_cas.sg.product.

Require Import CAS.theory.bs.product_product. 

Require Import CAS.theory.facts. 

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
           (brel_product rS rT) 
           (bop_product plusS plusT)
           (bop_product timesS timesT)
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
     bops_product_left_left_absorptive_decide S T rS rT plusS timesS plusT timesT 
        (A_eqv_nontrivial S rS eqvS)
        (A_eqv_nontrivial T rT eqvT)                
        (A_bs_left_left_absorptive_d S rS plusS timesS pS)
        (A_bs_left_left_absorptive_d T rT plusT timesT pT)
; A_bs_left_right_absorptive_d := 
     bops_product_left_right_absorptive_decide S T rS rT plusS timesS plusT timesT
        (A_eqv_nontrivial S rS eqvS)
        (A_eqv_nontrivial T rT eqvT)        
        (A_bs_left_right_absorptive_d S rS plusS timesS pS)
        (A_bs_left_right_absorptive_d T rT plusT timesT pT)
; A_bs_right_left_absorptive_d := 
     bops_product_right_left_absorptive_decide S T rS rT plusS timesS plusT timesT 
        (A_eqv_nontrivial S rS eqvS)
        (A_eqv_nontrivial T rT eqvT)        
        (A_bs_right_left_absorptive_d S rS plusS timesS pS)
        (A_bs_right_left_absorptive_d T rT plusT timesT pT)
; A_bs_right_right_absorptive_d := 
     bops_product_right_right_absorptive_decide S T rS rT plusS timesS plusT timesT 
        (A_eqv_nontrivial S rS eqvS)
        (A_eqv_nontrivial T rT eqvT)
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

Definition A_bs_product : ∀ (S T : Type),  A_bs S -> A_bs T -> A_bs (S * T) 
:= λ S T bsS bsT, 
{| 
     A_bs_eqv        := A_eqv_product S T 
                           (A_bs_eqv S bsS) 
                           (A_bs_eqv T bsT) 
   ; A_bs_plus       := bop_product 
                           (A_bs_plus S bsS) 
                           (A_bs_plus T bsT) 
   ; A_bs_times       := bop_product
                           (A_bs_times S bsS) 
                           (A_bs_times T bsT) 
   ; A_bs_plus_proofs := sg_proofs_product S T 
                           (A_eqv_eq S (A_bs_eqv S bsS)) 
                           (A_eqv_eq T (A_bs_eqv T bsT))
                           (A_bs_plus S bsS) 
                           (A_bs_plus T bsT) 
                           (A_eqv_proofs S (A_bs_eqv S bsS)) 
                           (A_eqv_proofs T (A_bs_eqv T bsT)) 
                           (A_bs_plus_proofs S bsS) 
                           (A_bs_plus_proofs T bsT) 
   ; A_bs_times_proofs := sg_proofs_product S T 
                           (A_eqv_eq S (A_bs_eqv S bsS)) 
                           (A_eqv_eq T (A_bs_eqv T bsT))
                           (A_bs_times S bsS) 
                           (A_bs_times T bsT) 
                           (A_eqv_proofs S (A_bs_eqv S bsS)) 
                           (A_eqv_proofs T (A_bs_eqv T bsT)) 
                           (A_bs_times_proofs S bsS) 
                           (A_bs_times_proofs T bsT) 
   ; A_bs_proofs    := bs_proofs_product S T 
                           (A_eqv_eq S (A_bs_eqv S bsS)) 
                           (A_eqv_eq T (A_bs_eqv T bsT))
                           (A_bs_plus S bsS) 
                           (A_bs_times S bsS) 
                           (A_bs_plus T bsT) 
                           (A_bs_times T bsT) 
                           (A_eqv_proofs S (A_bs_eqv S bsS)) 
                           (A_eqv_proofs T (A_bs_eqv T bsT)) 
                           (A_bs_proofs S bsS) 
                           (A_bs_proofs T bsT) 
   ; A_bs_ast        := Ast_bs_product(A_bs_ast S bsS, A_bs_ast T bsT)
|}. 



Definition semiring_proofs_product : 
  ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS mulS : binary_op S) (addT mulT : binary_op T), 
    eqv_proofs S rS ->
    eqv_proofs T rT -> 
    semiring_proofs S rS addS mulS ->
    semiring_proofs T rT addT mulT ->     
        semiring_proofs (S * T) (brel_product rS rT) (bop_product addS addT) (bop_product mulS mulT)
:= λ S T rS rT addS mulS addT mulT eqvS eqvT srS srT, 
{|
  A_semiring_left_distributive        :=
    bop_product_left_distributive S T rS rT addS mulS addT mulT  
        (A_semiring_left_distributive S rS addS mulS srS)
        (A_semiring_left_distributive T rT addT mulT srT)                                  
    
; A_semiring_right_distributive       :=
    bop_product_right_distributive S T rS rT addS mulS addT mulT  
        (A_semiring_right_distributive S rS addS mulS srS)
        (A_semiring_right_distributive T rT addT mulT srT)                                  

; A_semiring_plus_id_is_times_ann_d   :=
     bop_product_id_equals_ann_decide S T rS rT addS mulS addT mulT  
        (A_semiring_plus_id_is_times_ann_d S rS addS mulS srS)
        (A_semiring_plus_id_is_times_ann_d T rT addT mulT srT)                                  

; A_semiring_times_id_is_plus_ann_d   :=
     bop_product_id_equals_ann_decide S T rS rT mulS addS mulT addT  
        (A_semiring_times_id_is_plus_ann_d S rS addS mulS srS)
        (A_semiring_times_id_is_plus_ann_d T rT addT mulT srT)                                  
                                                                     
; A_semiring_left_left_absorptive_d   :=
    bops_product_left_left_absorptive_decide S T rS rT addS mulS addT mulT
        (A_eqv_nontrivial S rS eqvS)
        (A_eqv_nontrivial T rT eqvT)                
        (A_semiring_left_left_absorptive_d S rS addS mulS srS)
        (A_semiring_left_left_absorptive_d T rT addT mulT srT)                                  

; A_semiring_left_right_absorptive_d  :=
    bops_product_left_right_absorptive_decide S T rS rT addS mulS addT mulT
        (A_eqv_nontrivial S rS eqvS)
        (A_eqv_nontrivial T rT eqvT)                
        (A_semiring_left_right_absorptive_d S rS addS mulS srS)
        (A_semiring_left_right_absorptive_d T rT addT mulT srT)                                  

|}.


Definition A_semiring_product : ∀ (S T : Type),  A_semiring S ->  A_semiring T -> A_semiring (S * T) 
:= λ S T sr1 sr2, 
{| 
     A_semiring_eqv          := A_eqv_product S T (A_semiring_eqv S sr1) (A_semiring_eqv T sr2) 
   ; A_semiring_plus         := bop_product (A_semiring_plus S sr1) (A_semiring_plus T sr2) 
   ; A_semiring_times        := bop_product (A_semiring_times S sr1) (A_semiring_times T sr2) 
   ; A_semiring_plus_proofs  := sg_C_proofs_product S T
                                (A_eqv_eq S (A_semiring_eqv S sr1))
                                (A_eqv_eq T (A_semiring_eqv T sr2))                                                              
                                (A_semiring_plus S sr1)
                                (A_semiring_plus T sr2)                                 
                                (A_eqv_proofs S (A_semiring_eqv S sr1))
                                (A_eqv_proofs T (A_semiring_eqv T sr2))                                 
                                (A_semiring_plus_proofs S sr1)
                                (A_semiring_plus_proofs T sr2)                                 
   ; A_semiring_times_proofs := sg_proofs_product S T
                                (A_eqv_eq S (A_semiring_eqv S sr1))
                                (A_eqv_eq T (A_semiring_eqv T sr2))                                                              
                                (A_semiring_times S sr1)
                                (A_semiring_times T sr2)                                 
                                (A_eqv_proofs S (A_semiring_eqv S sr1))
                                (A_eqv_proofs T (A_semiring_eqv T sr2))                                 
                                (A_semiring_times_proofs S sr1)
                                (A_semiring_times_proofs T sr2)                                 

   ; A_semiring_proofs       := semiring_proofs_product S T
                                   (A_eqv_eq S (A_semiring_eqv S sr1))
                                   (A_eqv_eq T (A_semiring_eqv T sr2))                                                              
                                   (A_semiring_plus S sr1) (A_semiring_times S sr1)  
                                   (A_semiring_plus T sr2) (A_semiring_times T sr2)                                     
                                   (A_eqv_proofs S (A_semiring_eqv S sr1))
                                   (A_eqv_proofs T (A_semiring_eqv T sr2))                                   
                                   (A_semiring_proofs S sr1)
                                   (A_semiring_proofs T sr2)                                   
   ; A_semiring_ast  := Ast_semiring_product (A_semiring_ast S sr1, A_semiring_ast T sr2)
|}.


Definition A_dioid_product : ∀ (S T : Type),  A_dioid S ->  A_dioid T -> A_dioid (S * T) 
:= λ S T sr1 sr2, 
{| 
     A_dioid_eqv          := A_eqv_product S T (A_dioid_eqv S sr1) (A_dioid_eqv T sr2) 
   ; A_dioid_plus         := bop_product (A_dioid_plus S sr1) (A_dioid_plus T sr2) 
   ; A_dioid_times        := bop_product (A_dioid_times S sr1) (A_dioid_times T sr2) 
   ; A_dioid_plus_proofs  := sg_CI_proofs_product S T
                                (A_eqv_eq S (A_dioid_eqv S sr1))
                                (A_eqv_eq T (A_dioid_eqv T sr2))                                                              
                                (A_dioid_plus S sr1)
                                (A_dioid_plus T sr2)                                 
                                (A_eqv_proofs S (A_dioid_eqv S sr1))
                                (A_eqv_proofs T (A_dioid_eqv T sr2))                                 
                                (A_dioid_plus_proofs S sr1)
                                (A_dioid_plus_proofs T sr2)                                 
   ; A_dioid_times_proofs := sg_proofs_product S T
                                (A_eqv_eq S (A_dioid_eqv S sr1))
                                (A_eqv_eq T (A_dioid_eqv T sr2))                                                              
                                (A_dioid_times S sr1)
                                (A_dioid_times T sr2)                                 
                                (A_eqv_proofs S (A_dioid_eqv S sr1))
                                (A_eqv_proofs T (A_dioid_eqv T sr2))                                 
                                (A_dioid_times_proofs S sr1)
                                (A_dioid_times_proofs T sr2)                                 

   ; A_dioid_proofs       := semiring_proofs_product S T
                                   (A_eqv_eq S (A_dioid_eqv S sr1))
                                   (A_eqv_eq T (A_dioid_eqv T sr2))                                                              
                                   (A_dioid_plus S sr1) (A_dioid_times S sr1)  
                                   (A_dioid_plus T sr2) (A_dioid_times T sr2)                                     
                                   (A_eqv_proofs S (A_dioid_eqv S sr1))
                                   (A_eqv_proofs T (A_dioid_eqv T sr2))                                   
                                   (A_dioid_proofs S sr1)
                                   (A_dioid_proofs T sr2)                                   
   ; A_dioid_ast  := Ast_dioid_product (A_dioid_ast S sr1, A_dioid_ast T sr2)
|}.



Definition distributive_lattice_proofs_product : 
  ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS mulS : binary_op S) (addT mulT : binary_op T), 
    eqv_proofs S rS ->
    eqv_proofs T rT -> 
    distributive_lattice_proofs S rS addS mulS ->
    distributive_lattice_proofs T rT addT mulT ->     
        distributive_lattice_proofs (S * T) (brel_product rS rT) (bop_product addS addT) (bop_product mulS mulT)
:= λ S T rS rT addS mulS addT mulT eqvS eqvT srS srT, 
{|
  A_distributive_lattice_absorptive        := 
    bop_product_left_left_absorptive S T rS rT addS mulS addT mulT
        (A_distributive_lattice_absorptive S rS addS mulS srS)
        (A_distributive_lattice_absorptive T rT addT mulT srT)                                  
                                     
; A_distributive_lattice_absorptive_dual   :=
    bop_product_left_left_absorptive S T rS rT mulS addS mulT addT
        (A_distributive_lattice_absorptive_dual S rS addS mulS srS)
        (A_distributive_lattice_absorptive_dual T rT addT mulT srT)                                  

    
; A_distributive_lattice_distributive        :=
    bop_product_left_distributive S T rS rT addS mulS addT mulT  
        (A_distributive_lattice_distributive S rS addS mulS srS)
        (A_distributive_lattice_distributive T rT addT mulT srT)                                  
    
|}.

Definition A_distributive_lattice_product : ∀ (S T : Type),  A_distributive_lattice S ->  A_distributive_lattice T -> A_distributive_lattice (S * T) 
:= λ S T sr1 sr2, 
{| 
     A_distributive_lattice_eqv          := A_eqv_product S T (A_distributive_lattice_eqv S sr1) (A_distributive_lattice_eqv T sr2) 
   ; A_distributive_lattice_join         := bop_product (A_distributive_lattice_join S sr1) (A_distributive_lattice_join T sr2) 
   ; A_distributive_lattice_meet        := bop_product (A_distributive_lattice_meet S sr1) (A_distributive_lattice_meet T sr2) 
   ; A_distributive_lattice_join_proofs  := sg_CI_proofs_product S T
                                (A_eqv_eq S (A_distributive_lattice_eqv S sr1))
                                (A_eqv_eq T (A_distributive_lattice_eqv T sr2))                                                              
                                (A_distributive_lattice_join S sr1)
                                (A_distributive_lattice_join T sr2)                                 
                                (A_eqv_proofs S (A_distributive_lattice_eqv S sr1))
                                (A_eqv_proofs T (A_distributive_lattice_eqv T sr2))                                 
                                (A_distributive_lattice_join_proofs S sr1)
                                (A_distributive_lattice_join_proofs T sr2)                                 
   ; A_distributive_lattice_meet_proofs := sg_CI_proofs_product S T
                                (A_eqv_eq S (A_distributive_lattice_eqv S sr1))
                                (A_eqv_eq T (A_distributive_lattice_eqv T sr2))                                                              
                                (A_distributive_lattice_meet S sr1)
                                (A_distributive_lattice_meet T sr2)                                 
                                (A_eqv_proofs S (A_distributive_lattice_eqv S sr1))
                                (A_eqv_proofs T (A_distributive_lattice_eqv T sr2))                                 
                                (A_distributive_lattice_meet_proofs S sr1)
                                (A_distributive_lattice_meet_proofs T sr2)                                 

   ; A_distributive_lattice_proofs  := distributive_lattice_proofs_product S T
                                   (A_eqv_eq S (A_distributive_lattice_eqv S sr1))
                                   (A_eqv_eq T (A_distributive_lattice_eqv T sr2))                                                              
                                   (A_distributive_lattice_join S sr1) (A_distributive_lattice_meet S sr1)  
                                   (A_distributive_lattice_join T sr2) (A_distributive_lattice_meet T sr2)                                     
                                   (A_eqv_proofs S (A_distributive_lattice_eqv S sr1))
                                   (A_eqv_proofs T (A_distributive_lattice_eqv T sr2))                                   
                                   (A_distributive_lattice_proofs S sr1)
                                   (A_distributive_lattice_proofs T sr2)                                   
   ; A_distributive_lattice_ast  := Ast_distributive_lattice_product (A_distributive_lattice_ast S sr1, A_distributive_lattice_ast T sr2)
|}.




Definition lattice_proofs_product : 
  ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS mulS : binary_op S) (addT mulT : binary_op T), 
    eqv_proofs S rS ->
    eqv_proofs T rT -> 
    lattice_proofs S rS addS mulS ->
    lattice_proofs T rT addT mulT ->     
        lattice_proofs (S * T) (brel_product rS rT) (bop_product addS addT) (bop_product mulS mulT)
:= λ S T rS rT addS mulS addT mulT eqvS eqvT srS srT, 
{|
  A_lattice_absorptive        := 
    bop_product_left_left_absorptive S T rS rT addS mulS addT mulT
        (A_lattice_absorptive S rS addS mulS srS)
        (A_lattice_absorptive T rT addT mulT srT)                                  
                                     
; A_lattice_absorptive_dual   :=
    bop_product_left_left_absorptive S T rS rT mulS addS mulT addT
        (A_lattice_absorptive_dual S rS addS mulS srS)
        (A_lattice_absorptive_dual T rT addT mulT srT)                                  

    
; A_lattice_distributive_d        :=
     bop_product_left_distributive_decide S T rS rT addS mulS addT mulT 
        (A_eqv_nontrivial S rS eqvS)  
        (A_eqv_nontrivial T rT eqvT)  
        (A_lattice_distributive_d S rS addS mulS srS)
        (A_lattice_distributive_d T rT addT mulT  srT)

; A_lattice_distributive_dual_d        :=
     bop_product_left_distributive_decide S T rS rT mulS addS mulT addT 
        (A_eqv_nontrivial S rS eqvS)  
        (A_eqv_nontrivial T rT eqvT)  
        (A_lattice_distributive_dual_d S rS addS mulS srS)
        (A_lattice_distributive_dual_d T rT addT mulT  srT)
        
|}.


Definition A_lattice_product : ∀ (S T : Type),  A_lattice S ->  A_lattice T -> A_lattice (S * T) 
:= λ S T sr1 sr2, 
{| 
     A_lattice_eqv          := A_eqv_product S T (A_lattice_eqv S sr1) (A_lattice_eqv T sr2) 
   ; A_lattice_join         := bop_product (A_lattice_join S sr1) (A_lattice_join T sr2) 
   ; A_lattice_meet        := bop_product (A_lattice_meet S sr1) (A_lattice_meet T sr2) 
   ; A_lattice_join_proofs  := sg_CI_proofs_product S T
                                (A_eqv_eq S (A_lattice_eqv S sr1))
                                (A_eqv_eq T (A_lattice_eqv T sr2))                                                              
                                (A_lattice_join S sr1)
                                (A_lattice_join T sr2)                                 
                                (A_eqv_proofs S (A_lattice_eqv S sr1))
                                (A_eqv_proofs T (A_lattice_eqv T sr2))                                 
                                (A_lattice_join_proofs S sr1)
                                (A_lattice_join_proofs T sr2)                                 
   ; A_lattice_meet_proofs := sg_CI_proofs_product S T
                                (A_eqv_eq S (A_lattice_eqv S sr1))
                                (A_eqv_eq T (A_lattice_eqv T sr2))                                                              
                                (A_lattice_meet S sr1)
                                (A_lattice_meet T sr2)                                 
                                (A_eqv_proofs S (A_lattice_eqv S sr1))
                                (A_eqv_proofs T (A_lattice_eqv T sr2))                                 
                                (A_lattice_meet_proofs S sr1)
                                (A_lattice_meet_proofs T sr2)                                 

   ; A_lattice_proofs  := lattice_proofs_product S T
                                   (A_eqv_eq S (A_lattice_eqv S sr1))
                                   (A_eqv_eq T (A_lattice_eqv T sr2))                                                              
                                   (A_lattice_join S sr1) (A_lattice_meet S sr1)  
                                   (A_lattice_join T sr2) (A_lattice_meet T sr2)                                     
                                   (A_eqv_proofs S (A_lattice_eqv S sr1))
                                   (A_eqv_proofs T (A_lattice_eqv T sr2))                                   
                                   (A_lattice_proofs S sr1)
                                   (A_lattice_proofs T sr2)                                   
   ; A_lattice_ast  := Ast_lattice_product (A_lattice_ast S sr1, A_lattice_ast T sr2)
|}.
