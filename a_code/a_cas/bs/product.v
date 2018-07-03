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
    (plusT timesT : binary_op T) (s : S) (t : T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     bs_proofs S rS plusS timesS -> 
     bs_proofs T rT plusT timesT -> 
        bs_proofs (S * T) 
           (brel_product rS rT) 
           (bop_product plusS plusT)
           (bop_product timesS timesT)
:= λ S T rS rT plusS timesS plusT timesT s t eqvS eqvT pS pT, 
{|
  A_bs_left_distributive_d := 
     bop_product_left_distributive_decide S T rS rT s t plusS timesS plusT timesT 
        (A_bs_left_distributive_d S rS plusS timesS pS)
        (A_bs_left_distributive_d T rT plusT timesT pT)
; A_bs_right_distributive_d := 
     bop_product_right_distributive_decide S T rS rT s t plusS timesS plusT timesT 
        (A_bs_right_distributive_d S rS plusS timesS pS)
        (A_bs_right_distributive_d T rT plusT timesT pT)

; A_bs_left_left_absorptive_d := 
     bops_product_left_left_absorptive_decide S T rS rT s t plusS timesS plusT timesT 
        (A_bs_left_left_absorptive_d S rS plusS timesS pS)
        (A_bs_left_left_absorptive_d T rT plusT timesT pT)
; A_bs_left_right_absorptive_d := 
     bops_product_left_right_absorptive_decide S T rS rT s t plusS timesS plusT timesT 
        (A_bs_left_right_absorptive_d S rS plusS timesS pS)
        (A_bs_left_right_absorptive_d T rT plusT timesT pT)
; A_bs_right_left_absorptive_d := 
     bops_product_right_left_absorptive_decide S T rS rT s t plusS timesS plusT timesT 
        (A_bs_right_left_absorptive_d S rS plusS timesS pS)
        (A_bs_right_left_absorptive_d T rT plusT timesT pT)
; A_bs_right_right_absorptive_d := 
     bops_product_right_right_absorptive_decide S T rS rT s t plusS timesS plusT timesT
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
     A_bs_eqv        := A_eqv_product S T eqvS eqvT 
   ; A_bs_plus       := bop_product plusS plusT 
   ; A_bs_times      := bop_product timesS timesT 
   ; A_bs_plus_proofs := sg_proofs_product S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                           (A_bs_plus_proofs S bsS) 
                           (A_bs_plus_proofs T bsT) 
   ; A_bs_times_proofs := sg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                           (A_bs_times_proofs S bsS) 
                           (A_bs_times_proofs T bsT) 
   ; A_bs_proofs    := bs_proofs_product S T rS rT plusS timesS plusT timesT s t peqvS peqvT 
                           (A_bs_proofs S bsS) 
                           (A_bs_proofs T bsT) 
   ; A_bs_ast        := Ast_bs_product(A_bs_ast S bsS, A_bs_ast T bsT)
|}. 



Definition semiring_proofs_product : 
  ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS mulS : binary_op S) (addT mulT : binary_op T) (s : S) (t : T), 
    eqv_proofs S rS ->
    eqv_proofs T rT -> 
    semiring_proofs S rS addS mulS ->
    semiring_proofs T rT addT mulT ->     
        semiring_proofs (S * T) (brel_product rS rT) (bop_product addS addT) (bop_product mulS mulT)
:= λ S T rS rT addS mulS addT mulT s t eqvS eqvT srS srT, 
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
    bops_product_left_left_absorptive_decide S T rS rT s t addS mulS addT mulT
        (A_semiring_left_left_absorptive_d S rS addS mulS srS)
        (A_semiring_left_left_absorptive_d T rT addT mulT srT)                                  

; A_semiring_left_right_absorptive_d  :=
    bops_product_left_right_absorptive_decide S T rS rT s t addS mulS addT mulT
        (A_semiring_left_right_absorptive_d S rS addS mulS srS)
        (A_semiring_left_right_absorptive_d T rT addT mulT srT)                                  

|}.

Definition A_semiring_product : ∀ (S T : Type),  A_semiring S ->  A_semiring T -> A_semiring (S * T) 
:= λ S T sr1 sr2,
let eqvS   := A_semiring_eqv S sr1   in
let eqvT   := A_semiring_eqv T sr2   in
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
let plusS  := A_semiring_plus S sr1  in 
let plusT  := A_semiring_plus T sr2  in
let timesS := A_semiring_times S sr1 in 
let timesT := A_semiring_times T sr2 in 
{| 
     A_semiring_eqv          := A_eqv_product S T eqvS eqvT 
   ; A_semiring_plus         := bop_product plusS plusT 
   ; A_semiring_times        := bop_product timesS timesT 
   ; A_semiring_plus_proofs  := sg_C_proofs_product S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                                (A_semiring_plus_proofs S sr1)
                                (A_semiring_plus_proofs T sr2)                                 
   ; A_semiring_times_proofs := sg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                                (A_semiring_times_proofs S sr1)
                                (A_semiring_times_proofs T sr2)                                 
   ; A_semiring_proofs       := semiring_proofs_product S T rS rT plusS timesS plusT timesT s t peqvS peqvT 
                                   (A_semiring_proofs S sr1)
                                   (A_semiring_proofs T sr2)                                   
   ; A_semiring_ast  := Ast_semiring_product (A_semiring_ast S sr1, A_semiring_ast T sr2)
|}.

Definition A_dioid_product : ∀ (S T : Type),  A_dioid S ->  A_dioid T -> A_dioid (S * T) 
:= λ S T sr1 sr2,
let eqvS   := A_dioid_eqv S sr1   in
let eqvT   := A_dioid_eqv T sr2   in
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
let plusS  := A_dioid_plus S sr1  in 
let plusT  := A_dioid_plus T sr2  in
let timesS := A_dioid_times S sr1 in 
let timesT := A_dioid_times T sr2 in 
{| 
     A_dioid_eqv          := A_eqv_product S T eqvS eqvT 
   ; A_dioid_plus         := bop_product plusS plusT 
   ; A_dioid_times        := bop_product timesS timesT 
   ; A_dioid_plus_proofs  := sg_CI_proofs_product S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                                (A_dioid_plus_proofs S sr1)
                                (A_dioid_plus_proofs T sr2)                                 
   ; A_dioid_times_proofs := sg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                                (A_dioid_times_proofs S sr1)
                                (A_dioid_times_proofs T sr2)                                 
   ; A_dioid_proofs       := semiring_proofs_product S T rS rT plusS timesS plusT timesT s t peqvS peqvT 
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
let eqvS   := A_distributive_lattice_eqv S sr1   in
let eqvT   := A_distributive_lattice_eqv T sr2   in
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
let joinS  := A_distributive_lattice_join S sr1  in 
let joinT  := A_distributive_lattice_join T sr2  in
let meetS  := A_distributive_lattice_meet S sr1 in 
let meetT  := A_distributive_lattice_meet T sr2 in 
{| 
     A_distributive_lattice_eqv   := A_eqv_product S T eqvS eqvT 
   ; A_distributive_lattice_join  := bop_product joinS joinT 
   ; A_distributive_lattice_meet  := bop_product meetS meetT 
   ; A_distributive_lattice_join_proofs  := sg_CI_proofs_product S T rS rT joinS joinT s f t g Pf Pg peqvS peqvT  
                                (A_distributive_lattice_join_proofs S sr1)
                                (A_distributive_lattice_join_proofs T sr2)                                 
   ; A_distributive_lattice_meet_proofs := sg_CI_proofs_product S T rS rT meetS meetT s f t g Pf Pg peqvS peqvT  
                                (A_distributive_lattice_meet_proofs S sr1)
                                (A_distributive_lattice_meet_proofs T sr2)                                 
   ; A_distributive_lattice_proofs  := distributive_lattice_proofs_product S T rS rT joinS meetS joinT meetT peqvS peqvT  
                                   (A_distributive_lattice_proofs S sr1)
                                   (A_distributive_lattice_proofs T sr2)                                   
   ; A_distributive_lattice_ast  := Ast_distributive_lattice_product (A_distributive_lattice_ast S sr1, A_distributive_lattice_ast T sr2)
|}.


Definition lattice_proofs_product : 
  ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS mulS : binary_op S) (addT mulT : binary_op T) (s : S) (t : T), 
    eqv_proofs S rS ->
    eqv_proofs T rT -> 
    lattice_proofs S rS addS mulS ->
    lattice_proofs T rT addT mulT ->     
        lattice_proofs (S * T) (brel_product rS rT) (bop_product addS addT) (bop_product mulS mulT)
:= λ S T rS rT addS mulS addT mulT s t eqvS eqvT srS srT, 
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
     bop_product_left_distributive_decide S T rS rT s t addS mulS addT mulT 
        (A_lattice_distributive_d S rS addS mulS srS)
        (A_lattice_distributive_d T rT addT mulT  srT)

; A_lattice_distributive_dual_d        :=
     bop_product_left_distributive_decide S T rS rT s t mulS addS mulT addT 
        (A_lattice_distributive_dual_d S rS addS mulS srS)
        (A_lattice_distributive_dual_d T rT addT mulT  srT)
        
|}.


Definition A_lattice_product : ∀ (S T : Type),  A_lattice S ->  A_lattice T -> A_lattice (S * T) 
:= λ S T sr1 sr2,
let eqvS   := A_lattice_eqv S sr1   in
let eqvT   := A_lattice_eqv T sr2   in
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
let joinS  := A_lattice_join S sr1  in 
let joinT  := A_lattice_join T sr2  in
let meetS  := A_lattice_meet S sr1 in 
let meetT  := A_lattice_meet T sr2 in 
{| 
     A_lattice_eqv          := A_eqv_product S T eqvS eqvT 
   ; A_lattice_join         := bop_product joinS joinT 
   ; A_lattice_meet         := bop_product meetS meetT 
   ; A_lattice_join_proofs  := sg_CI_proofs_product S T rS rT joinS joinT s f t g Pf Pg peqvS peqvT  
                                (A_lattice_join_proofs S sr1)
                                (A_lattice_join_proofs T sr2)                                 
   ; A_lattice_meet_proofs := sg_CI_proofs_product S T rS rT meetS meetT s f t g Pf Pg peqvS peqvT  
                                (A_lattice_meet_proofs S sr1)
                                (A_lattice_meet_proofs T sr2)                                 
   ; A_lattice_proofs  := lattice_proofs_product S T rS rT joinS meetS joinT meetT s t peqvS peqvT  
                                   (A_lattice_proofs S sr1)
                                   (A_lattice_proofs T sr2)                                   
   ; A_lattice_ast  := Ast_lattice_product (A_lattice_ast S sr1, A_lattice_ast T sr2)
|}.
