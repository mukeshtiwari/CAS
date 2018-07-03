Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.a_code.proof_records.
Require Import CAS.a_code.a_cas_records.

Require Import CAS.theory.structures.lattice.


Definition lattice_proofs_dual (S: Type) (eqv : brel S) (join meet : binary_op S) :
          lattice_proofs S eqv join meet -> lattice_proofs S eqv meet join
:= λ pfs,
{|
   A_lattice_absorptive          := A_lattice_absorptive_dual S eqv join meet pfs
 ; A_lattice_absorptive_dual     := A_lattice_absorptive S eqv join meet pfs 
 ; A_lattice_distributive_d      := A_lattice_distributive_dual_d S eqv join meet pfs 
 ; A_lattice_distributive_dual_d := A_lattice_distributive_d S eqv join meet pfs 
|}.

Definition A_lattice_dual : ∀ (S : Type), A_lattice S -> A_lattice S
:= λ S lat,
{|  
  A_lattice_eqv          := A_lattice_eqv S lat 
; A_lattice_join         := A_lattice_meet S lat 
; A_lattice_meet         := A_lattice_join S lat 
; A_lattice_join_proofs  := A_lattice_meet_proofs S lat 
; A_lattice_meet_proofs  := A_lattice_join_proofs S lat 
; A_lattice_proofs       := lattice_proofs_dual S
                               (A_eqv_eq S (A_lattice_eqv S lat))
                               (A_lattice_join S lat)
                               (A_lattice_meet S lat)
                               (A_lattice_proofs S lat)   
; A_lattice_ast          := Ast_lattice_dual (A_lattice_ast S lat) 
|}.


Definition distributive_lattice_proofs_dual (S: Type) (rS : brel S) (join meet : binary_op S) :
  eqv_proofs S rS -> 
  sg_CI_proofs S rS join ->
  sg_CI_proofs S rS meet ->      
  distributive_lattice_proofs S rS join meet ->
           distributive_lattice_proofs S rS meet join
:= λ eqv p_join p_meet pfs,
{|
   A_distributive_lattice_absorptive        := A_distributive_lattice_absorptive_dual S rS join meet pfs
 ; A_distributive_lattice_absorptive_dual   := A_distributive_lattice_absorptive S rS join meet pfs 
 ; A_distributive_lattice_distributive      := lattice_distributive_implies_distributive_dual S rS
                                                  (A_eqv_reflexive S rS eqv)
                                                  (A_eqv_symmetric S rS eqv)
                                                  (A_eqv_transitive S rS eqv) 
                                                  join meet
                                                  (A_sg_CI_congruence S rS join p_join)
                                                  (A_sg_CI_associative S rS join p_join)
                                                  (A_sg_CI_commutative S rS meet p_meet)
                                                  (A_distributive_lattice_absorptive S rS join meet pfs)
                                                  (A_distributive_lattice_absorptive_dual S rS join meet pfs)
                                                  (A_distributive_lattice_distributive S rS join meet pfs) 
(*                                                                                        
 ; A_distributive_lattice_distributive      := A_distributive_lattice_distributive_dual S eqv join meet pfs
 ; A_distributive_lattice_distributive_dual := A_distributive_lattice_distributive S eqv join meet pfs                                                  
*)
|}.

Definition A_distributive_lattice_dual : ∀ (S : Type), A_distributive_lattice S -> A_distributive_lattice S
:= λ S lat,
{|  
  A_distributive_lattice_eqv          := A_distributive_lattice_eqv S lat 
; A_distributive_lattice_join         := A_distributive_lattice_meet S lat 
; A_distributive_lattice_meet         := A_distributive_lattice_join S lat 
; A_distributive_lattice_join_proofs  := A_distributive_lattice_meet_proofs S lat 
; A_distributive_lattice_meet_proofs  := A_distributive_lattice_join_proofs S lat 
; A_distributive_lattice_proofs       := distributive_lattice_proofs_dual S
                                             (A_eqv_eq S (A_distributive_lattice_eqv S lat))
                                             (A_distributive_lattice_join S lat)
                                             (A_distributive_lattice_meet S lat)
                                             (A_eqv_proofs S (A_distributive_lattice_eqv S lat))
                                             (A_distributive_lattice_join_proofs S lat)
                                             (A_distributive_lattice_meet_proofs S lat)                                             
                                             (A_distributive_lattice_proofs S lat)                                             
; A_distributive_lattice_ast          := Ast_distributive_lattice_dual (A_distributive_lattice_ast S lat) 
|}.
