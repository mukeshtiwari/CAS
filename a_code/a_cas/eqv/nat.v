Require Import CAS.code.basic_types. 
Require Import CAS.code.ast. 
Require Import CAS.code.brel. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.brel.eq_nat. 
Require Import CAS.a_code.proof_records.     
Require Import CAS.a_code.a_cas_records. 

Open Scope nat. 

Definition eqv_proofs_eq_nat : eqv_proofs nat brel_eq_nat (* (uop_id nat) *) 
:= {| 

(*
   ; A_eqv_rep_correct    := identity_rep_correct nat brel_eq_nat brel_eq_nat_reflexive 
   ; A_eqv_rep_idempotent := identity_rep_idempotent nat brel_eq_nat brel_eq_nat_reflexive 
*) 
     A_eqv_congruence  := brel_eq_nat_congruence 
   ; A_eqv_reflexive   := brel_eq_nat_reflexive 
   ; A_eqv_transitive  := brel_eq_nat_transitive 
   ; A_eqv_symmetric   := brel_eq_nat_symmetric
   |}. 


Definition A_eqv_nat : A_eqv nat
:= {| 
      A_eqv_eq     := brel_eq_nat 
    ; A_eqv_proofs := eqv_proofs_eq_nat

    ; A_eqv_witness     := 0
    ; A_eqv_new         := S
    ; A_eqv_not_trivial := brel_eq_nat_not_trivial                        

    ; A_eqv_data   := λ n, DATA_nat n 
    ; A_eqv_rep    := λ b, b 
    ; A_eqv_ast    := Ast_eqv_nat
   |}. 
