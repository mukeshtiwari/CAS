Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.data.
Require Import CAS.code.brel. 
Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.eqv_records.

(*
Definition eqv_certs_eq_bool : @eqv_certificates bool
:= {| 
     eqv_nontrivial := 
     {| 
       certify_nontrivial_witness  := Certify_Witness true 
     ; certify_nontrivial_negate   := Certify_Negate negb
     |} 
    ; eqv_congruence    := Assert_Brel_Congruence 
    ; eqv_reflexive     := Assert_Reflexive 
    ; eqv_symmetric     := Assert_Symmetric 
    ; eqv_transitive    := Assert_Transitive 
   |}. 
*) 
Definition eqv_eq_bool : @eqv bool 
:= {| 
      eqv_eq    := brel_eq_bool 
    ; eqv_witness := true 
    ; eqv_new   := negb 
(*    ; eqv_certs := eqv_certs_eq_bool *) 
    ; eqv_data  := λ b, DATA_bool b 
    ; eqv_rep   := λ b, b 
    ; eqv_ast   := Ast_eqv_bool 
|}. 

