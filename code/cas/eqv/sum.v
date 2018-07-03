Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.data.
Require Import CAS.code.brel. 
Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.eqv_records.

(*
Definition eqv_certs_sum : ∀ {S T : Type},  @eqv_certificates S -> @eqv_certificates T -> @eqv_certificates (S + T)
:= λ {S T} eqvS eqvT, 
   let wS := nontrivial_witness (eqv_nontrivial eqvS) in 
   let wT := nontrivial_witness (eqv_nontrivial eqvT) in 
   {| 
     eqv_nontrivial := 
     {| 
       certify_nontrivial_witness  := Certify_Witness (inl T wS) 
     ; certify_nontrivial_negate   := 
          Certify_Negate (λ (d : S + T), match d with | inl _ => inr wT | inr _ => inl wS end)
     |} 
    ; eqv_congruence    := Assert_Brel_Congruence 
    ; eqv_reflexive     := Assert_Reflexive 
    ; eqv_symmetric     := Assert_Symmetric 
    ; eqv_transitive    := Assert_Transitive 
   |}. 

*) 

Definition eqv_sum : ∀ {S T : Type},  @eqv S -> @eqv T -> @eqv (S + T)
:= λ {S T} eqvS eqvT, 
   {| 
     eqv_eq    := brel_sum (eqv_eq eqvS) (eqv_eq eqvT) 
   ; eqv_witness := inl (eqv_witness eqvS)
   ; eqv_new     := λ (d : S + T), match d with | inl _ => inr (eqv_witness eqvT) | inr _ => inl (eqv_witness eqvS) end
(*    ; eqv_certs := eqv_certs_sum (eqv_certs eqvS) (eqv_certs eqvT)  *) 
    ; eqv_data  := λ d, (match d with inl s => DATA_inl (eqv_data eqvS s) | inr t => DATA_inr (eqv_data eqvT t) end)
    ; eqv_rep   := λ d, (match d with inl s => inl _ (eqv_rep eqvS s) | inr t => inr _ (eqv_rep eqvT t) end)
    ; eqv_ast   := Ast_eqv_sum (eqv_ast eqvS, eqv_ast eqvT)
   |}. 
