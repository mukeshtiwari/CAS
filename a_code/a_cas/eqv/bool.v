Require Import CAS.code.basic_types. 
Require Import CAS.code.ast. 
Require Import CAS.code.brel. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.   
Require Import CAS.a_code.proof_records.     
Require Import CAS.a_code.a_cas_records. 
Require Import CAS.theory.brel.eq_bool. 

Definition eqv_proofs_eq_bool : eqv_proofs bool brel_eq_bool  (* (uop_id bool) *) 
:= {| 
     A_eqv_nontrivial     := brel_eq_bool_nontrivial
(*
   ; A_eqv_rep_correct    := identity_rep_correct bool brel_eq_bool brel_eq_bool_reflexive 
   ; A_eqv_rep_idempotent := identity_rep_idempotent bool brel_eq_bool brel_eq_bool_reflexive 
*) 

   ; A_eqv_congruence     := brel_eq_bool_congruence 
   ; A_eqv_reflexive      := brel_eq_bool_reflexive 
   ; A_eqv_transitive     := brel_eq_bool_transitive 
   ; A_eqv_symmetric      := brel_eq_bool_symmetric
   |}. 


Definition A_eqv_bool : A_eqv bool 
:= {| 
      A_eqv_eq     := brel_eq_bool 
    ; A_eqv_proofs := eqv_proofs_eq_bool
    ; A_eqv_data   := λ b, DATA_bool b 
    ; A_eqv_rep    := λ b, b 
    ; A_eqv_ast    := Ast_eqv_bool 
   |}. 
