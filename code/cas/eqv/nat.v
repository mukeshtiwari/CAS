Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.data.
Require Import CAS.code.brel. 
Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.eqv_records.

Open Scope nat. 

Definition eqv_certs_eq_nat : @eqv_certificates nat 
:= {| 
     eqv_nontrivial := 
     {| 
       certify_nontrivial_witness  := Certify_Witness 0 
     ; certify_nontrivial_negate   := Certify_Negate S (* (λ (i : nat), S i) *) 
     |} 
    ; eqv_congruence    := Assert_Brel_Congruence  
    ; eqv_reflexive     := Assert_Reflexive 
    ; eqv_symmetric     := Assert_Symmetric 
    ; eqv_transitive    := Assert_Transitive 
   |}. 


Definition eqv_eq_nat : eqv (S := nat)
:= {| 
      eqv_eq    := brel_eq_nat 
    ; eqv_certs := eqv_certs_eq_nat
    ; eqv_data  := λ n, DATA_nat n 
    ; eqv_rep   := λ b, b 
    ; eqv_ast   := Ast_eqv_nat
   |}. 
