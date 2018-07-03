Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.data.
Require Import CAS.code.brel. 
Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.eqv_records.
(*
Definition eqv_certs_add_constant : ∀ {S : Type}, cas_constant -> eqv_certificates (S := S) -> @eqv_certificates (with_constant S)
:= λ {S} c eqvS, 
   let w := nontrivial_witness (eqv_nontrivial eqvS) in 
   {| 
     eqv_nontrivial := 
     {| 
       certify_nontrivial_witness  := Certify_Witness (inr w)  
     ; certify_nontrivial_negate   := Certify_Negate (λ (d : with_constant S), 
                                          

     |} 
    ; eqv_congruence    := Assert_Brel_Congruence 
    ; eqv_reflexive     := Assert_Reflexive 
    ; eqv_symmetric     := Assert_Symmetric 
    ; eqv_transitive    := Assert_Transitive
   |}. 
*) 


Definition eqv_add_constant : ∀ {S : Type},  eqv (S := S) -> cas_constant -> @eqv (with_constant S)
:= λ {S} eqvS c, 
   {| 
     eqv_eq    := brel_add_constant (eqv_eq eqvS) c
    ; eqv_witness := inl c 
    ; eqv_new := (λ (d : with_constant S), match d with | inl _ => inr (eqv_witness eqvS) | inr _ => inl c end) 
(*    ; eqv_certs := eqv_certs_add_constant c (eqv_certs eqvS) *) 
    ; eqv_data  := λ d, (match d with inl s => DATA_inl(DATA_string s) | inr a => DATA_inr (eqv_data eqvS a) end)
    ; eqv_rep   := λ d, (match d with inl s => inl _ s  | inr s => inr _ (eqv_rep eqvS s) end )
    ; eqv_ast   := Ast_eqv_add_constant (c, eqv_ast eqvS)
   |}. 

