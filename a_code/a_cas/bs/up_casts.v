
Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.

Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.a_code.proof_records.
Require Import CAS.a_code.a_cas_records.

Require Import CAS.theory.facts. 


Definition semiring_proofs_to_bs_proofs :
  ∀ (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S),
       eqv_proofs S eq -> sg_C_proofs S eq plus -> semiring_proofs S eq plus times -> bs_proofs S eq plus times
:= λ S eq plus times eqv sg sr,
let tranS := A_eqv_transitive S eq eqv   in 
let plus_comm := A_sg_C_commutative S eq plus sg in   
{|
  A_bs_left_distributive_d      := inl _ (A_semiring_left_distributive S eq plus times sr)
; A_bs_right_distributive_d     := inl _ (A_semiring_right_distributive S eq plus times sr)

; A_bs_plus_id_is_times_ann_d   := A_semiring_plus_id_is_times_ann_d S eq plus times sr
; A_bs_times_id_is_plus_ann_d   := A_semiring_times_id_is_plus_ann_d S eq plus times sr

; A_bs_left_left_absorptive_d   := A_semiring_left_left_absorptive_d S eq plus times sr
; A_bs_left_right_absorptive_d  := A_semiring_left_right_absorptive_d S eq plus times sr
; A_bs_right_left_absorptive_d  := bops_left_left_absorptive_implies_right_left S eq plus times tranS plus_comm 
                                     (A_semiring_left_left_absorptive_d S eq plus times sr)
; A_bs_right_right_absorptive_d := bops_left_right_absorptive_implies_right_right S eq plus times tranS plus_comm 
                                     (A_semiring_left_right_absorptive_d S eq plus times sr)
|}.

Definition lattice_proofs_to_bs_proofs :
     ∀ (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S),
       lattice_proofs S eq plus times -> bs_proofs S eq plus times
:= λ S eq plus times lp,                                                    
{|
  A_bs_left_distributive_d      := 
; A_bs_right_distributive_d     :=

; A_bs_plus_id_is_times_ann_d   :=
; A_bs_times_id_is_plus_ann_d   := 

; A_bs_left_left_absorptive_d   := 
; A_bs_left_right_absorptive_d  := 
; A_bs_right_left_absorptive_d  := 
; A_bs_right_right_absorptive_d := 
|}.

Definition distributive_lattice_proofs_to_lattice_proofs :
     ∀ (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S),
             distributive_lattice_proofs S eq plus times -> lattice_proofs S eq plus times
:= λ S eq plus times dlp,                                                      
{|
  A_lattice_absorptive           :=
; A_lattice_absorptive_dual      :=
 
; A_lattice_distributive_d       := 
; A_lattice_distributive_dual_d  :=
|}. 


Definition distributive_lattice_proofs_to_semiring_proofs :
     ∀ (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S),
             distributive_lattice_proofs S eq plus times -> semiring_proofs S eq plus times
:= λ S eq plus times dlp,                                                        
{|
  A_semiring_left_distributive        := A_distributive_lattice_distributive S eq plus times dlp 
; A_semiring_right_distributive       := left_distributive_implies_right_distributive S eq plus times times_comm
                                              (A_distributive_lattice_distributive S eq plus times dlp)

; A_semiring_plus_id_is_times_ann_d   := 
; A_semiring_times_id_is_plus_ann_d   := 
                                                                     
; A_semiring_left_left_absorptive_d   := 
; A_semiring_left_right_absorptive_d  := 
|}.









