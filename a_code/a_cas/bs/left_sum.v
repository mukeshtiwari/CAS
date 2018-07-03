Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.

Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.a_code.proof_records.
Require Import CAS.a_code.a_cas_records.

Require Import CAS.a_code.a_cas.eqv.sum. 
Require Import CAS.a_code.a_cas.sg.left_sum.
Require Import CAS.a_code.a_cas.sg.right_sum.

Require Import CAS.theory.bs.left_sum_right_sum. 
Require Import CAS.theory.bs.right_sum_left_sum.

Require Import CAS.theory.facts. 


Definition bs_proofs_left_sum : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T) (s : S) (t : T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT ->
     sg_proofs T rT plusT ->      
     bs_proofs S rS plusS timesS -> 
     bs_proofs T rT plusT timesT -> 
        bs_proofs (S + T) 
           (brel_sum rS rT) 
           (bop_left_sum plusS plusT)
           (bop_right_sum timesS timesT)
:= λ S T rS rT plusS timesS plusT timesT s t eqvS eqvT sgT pS pT, 
{|
  A_bs_left_distributive_d :=
    bop_left_sum_right_sum_left_distributive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_reflexive T rT eqvT)                                                      
        (A_eqv_symmetric T rT eqvT)                                                      
        (A_sg_idempotent_d T rT plusT sgT)
        (A_bs_left_distributive_d S rS plusS timesS pS)
        (A_bs_left_distributive_d T rT plusT timesT pT)
        (A_bs_left_left_absorptive_d T rT plusT timesT pT)
        (A_bs_right_left_absorptive_d T rT plusT timesT pT)        

; A_bs_right_distributive_d := 
    bop_left_sum_right_sum_right_distributive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_reflexive T rT eqvT)                                                      
        (A_eqv_symmetric T rT eqvT)                                                      
        (A_sg_idempotent_d T rT plusT sgT)
        (A_bs_right_distributive_d S rS plusS timesS pS)
        (A_bs_right_distributive_d T rT plusT timesT pT)
        (A_bs_left_right_absorptive_d T rT plusT timesT pT)
        (A_bs_right_right_absorptive_d T rT plusT timesT pT)        

; A_bs_left_left_absorptive_d := 
    bop_left_sum_right_sum_left_left_absorptive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_symmetric T rT eqvT)                                                      
        (A_sg_idempotent_d T rT plusT sgT)
        (A_bs_left_left_absorptive_d S rS plusS timesS pS)
        (A_bs_left_left_absorptive_d T rT plusT timesT pT)        

; A_bs_left_right_absorptive_d := 
    bop_left_sum_right_sum_left_right_absorptive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_symmetric T rT eqvT)                                                      
        (A_sg_idempotent_d T rT plusT sgT)
        (A_bs_left_right_absorptive_d S rS plusS timesS pS)
        (A_bs_left_right_absorptive_d T rT plusT timesT pT)        

; A_bs_right_left_absorptive_d :=
    bop_left_sum_right_sum_right_left_absorptive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_symmetric T rT eqvT)                                                      
        (A_sg_idempotent_d T rT plusT sgT)
        (A_bs_right_left_absorptive_d S rS plusS timesS pS)
        (A_bs_right_left_absorptive_d T rT plusT timesT pT)        
    
; A_bs_right_right_absorptive_d := 
    bop_left_sum_right_sum_right_right_absorptive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_symmetric T rT eqvT)                                                      
        (A_sg_idempotent_d T rT plusT sgT)
        (A_bs_right_right_absorptive_d S rS plusS timesS pS)
        (A_bs_right_right_absorptive_d T rT plusT timesT pT)        

; A_bs_plus_id_is_times_ann_d :=
    bop_left_sum_right_sum_id_equals_ann_decide S T rS rT t plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_reflexive T rT eqvT)                                                      
        (A_bs_plus_id_is_times_ann_d T rT plusT timesT pT)        

; A_bs_times_id_is_plus_ann_d :=  
    bop_right_sum_left_sum_id_equals_ann_decide S T rS rT s timesS plusS timesT plusT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_reflexive T rT eqvT)                                                      
        (A_bs_times_id_is_plus_ann_d S rS plusS timesS pS)        
|}.



Definition lattice_proofs_left_sum : 
  ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS mulS : binary_op S) (addT mulT : binary_op T) (s : S) (t : T), 
    eqv_proofs S rS ->
    eqv_proofs T rT ->
    sg_CI_proofs S rS mulS ->             
    sg_CI_proofs T rT addT ->     
    lattice_proofs S rS addS mulS ->
    lattice_proofs T rT addT mulT ->     
        lattice_proofs (S + T) (brel_sum rS rT) (bop_left_sum addS addT) (bop_right_sum mulS mulT)
:= λ S T rS rT addS mulS addT mulT s t eqvS eqvT p_mulS p_addT srS srT, 
{|
  A_lattice_absorptive        := 
    bop_left_sum_right_sum_left_left_absorptive S T rS rT addS mulS addT mulT
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric T rT eqvT)
        (A_sg_CI_idempotent T rT addT p_addT)                                          
        (A_lattice_absorptive S rS addS mulS srS)
        (A_lattice_absorptive T rT addT mulT srT)
                                     
; A_lattice_absorptive_dual   :=
    bop_right_sum_left_sum_left_left_absorptive S T rS rT mulS addS mulT addT
        (A_eqv_symmetric S rS eqvS)
        (A_eqv_reflexive T rT eqvT)
        (A_sg_CI_idempotent S rS mulS p_mulS)                                          
        (A_lattice_absorptive_dual S rS addS mulS srS)
        (A_lattice_absorptive_dual T rT addT mulT srT)

; A_lattice_distributive_d        :=
  bop_left_sum_right_sum_left_distributive_decide S T rS rT s addS mulS addT mulT
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_reflexive T rT eqvT)
        (A_eqv_symmetric T rT eqvT)
        (inl _ (A_sg_CI_idempotent T rT addT p_addT))                                        
        (A_lattice_distributive_d S rS addS mulS srS)
        (A_lattice_distributive_d T rT addT mulT  srT)
        (inl _ (A_lattice_absorptive T rT addT mulT srT))
        (inl _ (bops_left_left_absorptive_implies_right_left T rT addT mulT
                  (A_eqv_transitive T rT eqvT)
                  (A_sg_CI_commutative T rT addT p_addT)
                  (A_lattice_absorptive T rT addT mulT srT)
               )
        )

; A_lattice_distributive_dual_d        :=
  bop_right_sum_left_sum_left_distributive_decide S T rS rT t mulS addS mulT addT
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (A_eqv_reflexive T rT eqvT)
        (inl _ (A_sg_CI_idempotent S rS mulS p_mulS))                                        
        (A_lattice_distributive_dual_d S rS addS mulS srS)
        (A_lattice_distributive_dual_d T rT addT mulT  srT)
        (inl _ (A_lattice_absorptive_dual S rS addS mulS srS))
        (inl _ (bops_left_left_absorptive_implies_right_left S rS mulS addS 
                  (A_eqv_transitive S rS eqvS)
                  (A_sg_CI_commutative S rS mulS p_mulS)
                  (A_lattice_absorptive_dual S rS addS mulS srS)
               )
        )
        
|}.

Definition distributive_lattice_proofs_left_sum : 
  ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS mulS : binary_op S) (addT mulT : binary_op T), 
    eqv_proofs S rS ->
    eqv_proofs T rT ->
    sg_CI_proofs S rS mulS ->             
    sg_CI_proofs T rT addT ->     
    distributive_lattice_proofs S rS addS mulS ->
    distributive_lattice_proofs T rT addT mulT ->     
        distributive_lattice_proofs (S + T) (brel_sum rS rT) (bop_left_sum addS addT) (bop_right_sum mulS mulT)
:= λ S T rS rT addS mulS addT mulT eqvS eqvT p_mulS p_addT srS srT, 
{|
  A_distributive_lattice_absorptive        := 
    bop_left_sum_right_sum_left_left_absorptive S T rS rT addS mulS addT mulT
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric T rT eqvT)
        (A_sg_CI_idempotent T rT addT p_addT)                                          
        (A_distributive_lattice_absorptive S rS addS mulS srS)
        (A_distributive_lattice_absorptive T rT addT mulT srT)
                                     
; A_distributive_lattice_absorptive_dual   :=
    bop_right_sum_left_sum_left_left_absorptive S T rS rT mulS addS mulT addT
        (A_eqv_symmetric S rS eqvS)
        (A_eqv_reflexive T rT eqvT)
        (A_sg_CI_idempotent S rS mulS p_mulS)                                          
        (A_distributive_lattice_absorptive_dual S rS addS mulS srS)
        (A_distributive_lattice_absorptive_dual T rT addT mulT srT)
    
; A_distributive_lattice_distributive        :=
  bop_left_sum_right_sum_left_distributive S T rS rT addS mulS addT mulT
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_reflexive T rT eqvT)
        (A_eqv_symmetric T rT eqvT)
        (A_sg_CI_idempotent T rT addT p_addT)
        (A_distributive_lattice_distributive S rS addS mulS srS)
        (A_distributive_lattice_distributive T rT addT mulT  srT)
        (A_distributive_lattice_absorptive T rT addT mulT srT)
        (bops_left_left_absorptive_implies_right_left T rT addT mulT
            (A_eqv_transitive T rT eqvT)
            (A_sg_CI_commutative T rT addT p_addT)
            (A_distributive_lattice_absorptive T rT addT mulT srT)
        )
|}.


Definition A_bs_left_sum : ∀ (S T : Type),  A_bs S -> A_bs T -> A_bs (S + T) 
:= λ S T bsS bsT, 
let eqvS   := A_bs_eqv S bsS   in
let eqvT   := A_bs_eqv T bsT   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let f      := A_eqv_new S eqvS in
let Pf     := A_eqv_not_trivial S eqvS in
let t      := A_eqv_witness T eqvT in
let g      := A_eqv_new T eqvT in
let Pg     := A_eqv_not_trivial T eqvT in
let plusS  := A_bs_plus S bsS  in 
let plusT  := A_bs_plus T bsT  in
let timesS := A_bs_times S bsS in 
let timesT := A_bs_times T bsT in 
{| 
     A_bs_eqv        := A_eqv_sum S T eqvS eqvT 
   ; A_bs_plus       := bop_left_sum plusS plusT 
   ; A_bs_times       := bop_right_sum timesS timesT 
   ; A_bs_plus_proofs := sg_proofs_left_sum S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                           (A_bs_plus_proofs S bsS) 
                           (A_bs_plus_proofs T bsT) 
   ; A_bs_times_proofs := sg_proofs_right_sum S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                           (A_bs_times_proofs S bsS) 
                           (A_bs_times_proofs T bsT) 
   ; A_bs_proofs    := bs_proofs_left_sum S T rS rT plusS timesS plusT timesT s t peqvS peqvT 
                           (A_bs_plus_proofs T bsT)                            
                           (A_bs_proofs S bsS) 
                           (A_bs_proofs T bsT) 
   ; A_bs_ast        := Ast_bs_left_sum(A_bs_ast S bsS, A_bs_ast T bsT)
|}. 


Definition A_lattice_left_sum : ∀ (S T : Type),  A_lattice S ->  A_lattice T -> A_lattice (S + T) 
:= λ S T sr1 sr2,
let eqvS   := A_lattice_eqv S sr1   in
let eqvT   := A_lattice_eqv T sr2   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let t      := A_eqv_witness T eqvT in
let joinS  := A_lattice_join S sr1  in 
let joinT  := A_lattice_join T sr2  in
let meetS  := A_lattice_meet S sr1 in 
let meetT  := A_lattice_meet T sr2 in 
{| 
     A_lattice_eqv          := A_eqv_sum S T eqvS eqvT
   ; A_lattice_join         := bop_left_sum joinS joinT
   ; A_lattice_meet         := bop_right_sum meetS meetT 
   ; A_lattice_join_proofs  := sg_CI_proofs_left_sum S T rS rT joinS joinT s t peqvS peqvT 
                                (A_lattice_join_proofs S sr1)
                                (A_lattice_join_proofs T sr2)                                 
   ; A_lattice_meet_proofs := sg_CI_proofs_right_sum S T rS rT meetS meetT s t peqvS peqvT 
                                (A_lattice_meet_proofs S sr1)
                                (A_lattice_meet_proofs T sr2)                                 
   ; A_lattice_proofs  := lattice_proofs_left_sum S T rS rT joinS meetS joinT meetT s t peqvS peqvT 
                                   (A_lattice_meet_proofs S sr1)
                                   (A_lattice_join_proofs T sr2)                                                                      
                                   (A_lattice_proofs S sr1)
                                   (A_lattice_proofs T sr2)                                   
   ; A_lattice_ast  := Ast_lattice_left_sum (A_lattice_ast S sr1, A_lattice_ast T sr2)
|}.


Definition A_distributive_lattice_left_sum : ∀ (S T : Type),  A_distributive_lattice S ->  A_distributive_lattice T -> A_distributive_lattice (S + T) 
:= λ S T sr1 sr2,
let eqvS   := A_distributive_lattice_eqv S sr1   in
let eqvT   := A_distributive_lattice_eqv T sr2   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let t      := A_eqv_witness T eqvT in
let joinS  := A_distributive_lattice_join S sr1  in 
let joinT  := A_distributive_lattice_join T sr2  in
let meetS  := A_distributive_lattice_meet S sr1 in 
let meetT  := A_distributive_lattice_meet T sr2 in 
{| 
     A_distributive_lattice_eqv          := A_eqv_sum S T eqvS eqvT
   ; A_distributive_lattice_join         := bop_left_sum joinS joinT
   ; A_distributive_lattice_meet        := bop_right_sum meetS meetT 
   ; A_distributive_lattice_join_proofs  := sg_CI_proofs_left_sum S T rS rT joinS joinT s t peqvS peqvT 
                                (A_distributive_lattice_join_proofs S sr1)
                                (A_distributive_lattice_join_proofs T sr2)                                 
   ; A_distributive_lattice_meet_proofs := sg_CI_proofs_right_sum S T rS rT meetS meetT s t peqvS peqvT 
                                (A_distributive_lattice_meet_proofs S sr1)
                                (A_distributive_lattice_meet_proofs T sr2)                                 
   ; A_distributive_lattice_proofs  := distributive_lattice_proofs_left_sum S T rS rT joinS meetS joinT meetT peqvS peqvT 
                                   (A_distributive_lattice_meet_proofs S sr1)
                                   (A_distributive_lattice_join_proofs T sr2)                                                                      
                                   (A_distributive_lattice_proofs S sr1)
                                   (A_distributive_lattice_proofs T sr2)                                   
   ; A_distributive_lattice_ast  := Ast_distributive_lattice_left_sum (A_distributive_lattice_ast S sr1, A_distributive_lattice_ast T sr2)
|}.

                                   
