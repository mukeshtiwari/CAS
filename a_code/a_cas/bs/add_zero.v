
Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.

Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.a_code.proof_records.
Require Import CAS.a_code.a_cas_records.

Require Import CAS.a_code.a_cas.eqv.add_constant. 
Require Import CAS.a_code.a_cas.sg.add_id.
Require Import CAS.a_code.a_cas.sg.add_ann.

Require Import CAS.theory.bs.add_ann_add_id.
Require Import CAS.theory.bs.add_id_add_ann.

Require Import CAS.theory.facts. 

Definition bs_proofs_add_zero : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (plusS timesS : binary_op S), 
     eqv_proofs S rS -> 
     bs_proofs S rS plusS timesS -> 
        bs_proofs 
           (with_constant S) 
           (brel_add_constant rS c)
           (bop_add_id plusS c)
           (bop_add_ann timesS c)
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
    bops_add_zero_ann_equals_id_decide S rS c plusS timesS 
      (A_eqv_reflexive S rS eqvS)
      (A_eqv_nontrivial S rS eqvS)
      (A_bs_times_id_is_plus_ann_d S rS plusS timesS pS)
|}. 

Definition A_bs_add_zero : ∀ (S : Type),  A_bs S -> cas_constant -> A_bs (with_constant S) 
:= λ S bsS c, 
{| 
     A_bs_eqv          := A_eqv_add_constant S (A_bs_eqv S bsS) c 
   ; A_bs_plus         := bop_add_id  (A_bs_plus S bsS) c
   ; A_bs_times        := bop_add_ann  (A_bs_times S bsS) c
   ; A_bs_plus_proofs  := sg_proofs_add_id S 
                                (A_eqv_eq S (A_bs_eqv S bsS)) c 
                                (A_bs_plus S bsS) 
                                (A_eqv_proofs S (A_bs_eqv S bsS)) 
                                (A_bs_plus_proofs S bsS) 
   ; A_bs_times_proofs := sg_proofs_add_ann S 
                                (A_eqv_eq S (A_bs_eqv S bsS)) c 
                                (A_bs_times S bsS)  
                                (A_eqv_proofs S (A_bs_eqv S bsS)) 
                                (A_bs_times_proofs S bsS) 
   ; A_bs_proofs       := bs_proofs_add_zero S _ c 
                                (A_bs_plus S bsS) 
                                (A_bs_times S bsS)  
                                (A_eqv_proofs S (A_bs_eqv S bsS)) 
                                (A_bs_proofs S bsS)
   ; A_bs_ast          := Ast_bs_add_zero (c, A_bs_ast S bsS)
|}. 


Definition distributive_lattice_proofs_add_zero : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (join meet : binary_op S), 
     eqv_proofs S rS -> 
     sg_CI_proofs S rS meet ->      
     distributive_lattice_proofs S rS join meet -> 
        distributive_lattice_proofs 
           (with_constant S) 
           (brel_add_constant rS c)
           (bop_add_id join c)
           (bop_add_ann meet c)
:= λ S rS c join meet eqvS p_meet p_dl, 
{|
  A_distributive_lattice_absorptive        := 
    bops_add_id_add_ann_left_left_absorptive S rS c join meet
       (A_eqv_reflexive S rS eqvS)
       (A_distributive_lattice_absorptive S rS join meet p_dl)
; A_distributive_lattice_absorptive_dual   := 
    bops_add_ann_add_id_left_left_absorptive S rS c meet join
      (A_eqv_symmetric S rS eqvS)
      (A_sg_CI_idempotent S rS meet p_meet)                                             
      (A_distributive_lattice_absorptive_dual S rS join meet p_dl)                                                                        
; A_distributive_lattice_distributive      := 
    bops_add_id_add_ann_left_distributive S rS c join meet
        (A_eqv_reflexive S rS eqvS)
        (A_distributive_lattice_distributive S rS join meet p_dl)
(*        
; A_distributive_lattice_distributive_dual := 
    bops_add_ann_add_id_left_distributive S rS c meet join
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (A_sg_CI_idempotent S rS meet p_meet)
        (A_distributive_lattice_absorptive_dual S rS join meet p_dl)
        (bops_left_right_absorptive_implies_right_left S rS meet join
            (A_eqv_reflexive S rS eqvS)                                                       
            (A_eqv_transitive S rS eqvS)
            (A_sg_CI_congruence S rS meet p_meet)
            (A_sg_CI_commutative S rS meet p_meet)
            (A_sg_CI_commutative S rS join p_join)
            (bops_left_left_absorptive_implies_left_right S rS meet join
                (A_eqv_reflexive S rS eqvS)                                                          
                (A_eqv_transitive S rS eqvS)
                (A_sg_CI_congruence S rS meet p_meet)
                (A_sg_CI_commutative S rS join p_join)
                (A_distributive_lattice_absorptive_dual S rS join meet p_dl)
            )                                          
        )
        (A_distributive_lattice_distributive_dual S rS join meet p_dl)        
*)
|}.



Definition A_distributive_lattice_add_zero : ∀ (S : Type),  A_distributive_lattice S -> cas_constant -> A_distributive_lattice (with_constant S) 
:= λ S bsS c, 
{| 
     A_distributive_lattice_eqv          := A_eqv_add_constant S (A_distributive_lattice_eqv S bsS) c 
   ; A_distributive_lattice_join         := bop_add_id (A_distributive_lattice_join S bsS) c
   ; A_distributive_lattice_meet        := bop_add_ann (A_distributive_lattice_meet S bsS) c
   ; A_distributive_lattice_join_proofs  := sg_CI_proofs_add_id S 
                                (A_eqv_eq S (A_distributive_lattice_eqv S bsS)) c 
                                (A_distributive_lattice_join S bsS) 
                                (A_eqv_proofs S (A_distributive_lattice_eqv S bsS)) 
                                (A_distributive_lattice_join_proofs S bsS) 
   ; A_distributive_lattice_meet_proofs := sg_CI_proofs_add_ann S 
                                (A_eqv_eq S (A_distributive_lattice_eqv S bsS)) c 
                                (A_distributive_lattice_meet S bsS)  
                                (A_eqv_proofs S (A_distributive_lattice_eqv S bsS)) 
                                (A_distributive_lattice_meet_proofs S bsS) 
   ; A_distributive_lattice_proofs       := distributive_lattice_proofs_add_zero S _ c 
                                (A_distributive_lattice_join S bsS) 
                                (A_distributive_lattice_meet S bsS)  
                                (A_eqv_proofs S (A_distributive_lattice_eqv S bsS)) 
                                (A_distributive_lattice_meet_proofs S bsS)                                 
                                (A_distributive_lattice_proofs S bsS)
   ; A_distributive_lattice_ast  := Ast_distributive_lattice_add_zero (c, A_distributive_lattice_ast S bsS)
|}. 


Definition lattice_proofs_add_zero : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (join meet : binary_op S), 
     eqv_proofs S rS ->
     sg_CI_proofs S rS join ->          
     sg_CI_proofs S rS meet ->      
     lattice_proofs S rS join meet -> 
        lattice_proofs 
           (with_constant S) 
           (brel_add_constant rS c)
           (bop_add_id join c)
           (bop_add_ann meet c)
:= λ S rS c join meet eqvS p_join p_meet p_dl, 
{|
  A_lattice_absorptive        := 
    bops_add_id_add_ann_left_left_absorptive S rS c join meet
       (A_eqv_reflexive S rS eqvS)
       (A_lattice_absorptive S rS join meet p_dl)
; A_lattice_absorptive_dual   := 
    bops_add_ann_add_id_left_left_absorptive S rS c meet join
      (A_eqv_symmetric S rS eqvS)
      (A_sg_CI_idempotent S rS meet p_meet)                                             
      (A_lattice_absorptive_dual S rS join meet p_dl)                                                                        
; A_lattice_distributive_d      := 
     bops_add_zero_left_distributive_decide S rS c join meet 
        (A_eqv_reflexive S rS eqvS)
        (A_lattice_distributive_d S rS join meet p_dl)
; A_lattice_distributive_dual_d      := 
     bops_add_one_left_distributive_decide S rS c meet join
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (inl _ (A_sg_CI_idempotent S rS meet p_meet))
        (inl _ (A_lattice_absorptive_dual S rS join meet p_dl))
        (inl _ (bops_left_right_absorptive_implies_right_left S rS meet join
                  (A_eqv_reflexive S rS eqvS)                                                       
                  (A_eqv_transitive S rS eqvS)
                  (A_sg_CI_congruence S rS meet p_meet)
                  (A_sg_CI_commutative S rS meet p_meet)
                  (A_sg_CI_commutative S rS join p_join)
                  (bops_left_left_absorptive_implies_left_right S rS meet join
                        (A_eqv_reflexive S rS eqvS)                                                          
                        (A_eqv_transitive S rS eqvS)
                        (A_sg_CI_congruence S rS meet p_meet)
                        (A_sg_CI_commutative S rS join p_join)
                        (A_lattice_absorptive_dual S rS join meet p_dl)
                  ) 
               )
        ) 
        (A_lattice_distributive_dual_d S rS join meet p_dl)         
|}.


Definition A_lattice_add_zero : ∀ (S : Type),  A_lattice S -> cas_constant -> A_lattice (with_constant S) 
:= λ S bsS c, 
{| 
     A_lattice_eqv          := A_eqv_add_constant S (A_lattice_eqv S bsS) c 
   ; A_lattice_join         := bop_add_id (A_lattice_join S bsS) c
   ; A_lattice_meet        := bop_add_ann (A_lattice_meet S bsS) c
   ; A_lattice_join_proofs  := sg_CI_proofs_add_id S 
                                (A_eqv_eq S (A_lattice_eqv S bsS)) c 
                                (A_lattice_join S bsS) 
                                (A_eqv_proofs S (A_lattice_eqv S bsS)) 
                                (A_lattice_join_proofs S bsS) 
   ; A_lattice_meet_proofs := sg_CI_proofs_add_ann S 
                                (A_eqv_eq S (A_lattice_eqv S bsS)) c 
                                (A_lattice_meet S bsS)  
                                (A_eqv_proofs S (A_lattice_eqv S bsS)) 
                                (A_lattice_meet_proofs S bsS) 
   ; A_lattice_proofs       := lattice_proofs_add_zero S _ c 
                                (A_lattice_join S bsS) 
                                (A_lattice_meet S bsS)  
                                (A_eqv_proofs S (A_lattice_eqv S bsS))
                                (A_lattice_join_proofs S bsS)                                                                 
                                (A_lattice_meet_proofs S bsS)                                 
                                (A_lattice_proofs S bsS)
   ; A_lattice_ast  := Ast_lattice_add_zero (c, A_lattice_ast S bsS)
|}. 
