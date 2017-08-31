Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.data.
Require Import CAS.code.brel. 
Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.eqv_records.

Definition eqv_certs_brel_list : ∀ {S : Type},  eqv_certificates (S := S) -> @eqv_certificates (list S)
:= λ {S} eqvS, 
   let w := nontrivial_witness (eqv_nontrivial eqvS) in 
   {| 
     eqv_nontrivial := 
     {| 
       certify_nontrivial_witness  := Certify_Witness nil  
     ; certify_nontrivial_negate   := Certify_Negate (λ (l : list S), w :: l)
     |} 
    ; eqv_congruence    := Assert_Brel_Congruence 
    ; eqv_reflexive     := Assert_Reflexive 
    ; eqv_symmetric     := Assert_Symmetric 
    ; eqv_transitive    := Assert_Transitive 
   |}. 



Definition eqv_list : ∀ {S : Type},  eqv (S := S) -> @eqv (list S)
:= λ {S} eqvS, 
   {| 
      eqv_eq    := brel_list (eqv_eq eqvS) 
    ; eqv_certs := eqv_certs_brel_list (eqv_certs eqvS)
    ; eqv_data  := λ l, DATA_list (List.map (eqv_data eqvS) l)
    ; eqv_rep   := λ l, List.map (eqv_rep eqvS) l
    ; eqv_ast   := Ast_eqv_list (eqv_ast eqvS)
   |}. 
