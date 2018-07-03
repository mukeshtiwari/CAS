Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.data.
Require Import CAS.code.brel. 
Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.eqv_records.

(*
Definition assert_product_nontrivial : ∀ {S T : Type},  @assert_nontrivial S -> @assert_nontrivial T -> @assert_nontrivial (S * T)
:= λ {S T} ntS ntT, 
  match certify_nontrivial_negate ntS, certify_nontrivial_negate ntT with 
  | Certify_Negate f, Certify_Negate g => 
    {| 
       certify_nontrivial_witness  := Certify_Witness (nontrivial_witness ntS, nontrivial_witness ntT)
     ; certify_nontrivial_negate   :=  Certify_Negate (λ (p : S * T), let (x, y) := p in (f x, g y))
   |}
  end. 


Definition eqv_certs_product : ∀ {S T : Type},  @eqv_certificates S -> @eqv_certificates T -> @eqv_certificates (S * T)
:= λ {S T} eqvS eqvT, 
   {| 
      eqv_nontrivial := assert_product_nontrivial (eqv_nontrivial eqvS) (eqv_nontrivial eqvT)
    ; eqv_congruence    := Assert_Brel_Congruence 
    ; eqv_reflexive     := Assert_Reflexive 
    ; eqv_symmetric     := Assert_Symmetric 
    ; eqv_transitive    := Assert_Transitive 
   |}. 

*) 

Definition eqv_product : ∀ {S T : Type},  @eqv S -> @eqv T -> @eqv (S * T)
:= λ {S T} eqvS eqvT, 
   {| 
     eqv_eq    := brel_product (eqv_eq eqvS) (eqv_eq eqvT) 
    ; eqv_witness := (eqv_witness eqvS, eqv_witness eqvT)
    ; eqv_new     := λ (p : S * T), let (x, y) := p in ((eqv_new eqvS) x, y)
(*    ; eqv_certs := eqv_certs_product (eqv_certs eqvS) (eqv_certs eqvT) *) 
    ; eqv_data  := λ p, DATA_pair (eqv_data eqvS (fst p), eqv_data eqvT (snd p))
    ; eqv_rep   := λ p, (eqv_rep eqvS (fst p), eqv_rep eqvT (snd p))
    ; eqv_ast  := Ast_eqv_product (eqv_ast eqvS, eqv_ast eqvT)
   |}. 

