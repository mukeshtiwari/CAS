Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.data.
Require Import CAS.code.brel. 
Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.eqv_records.

Definition eqv_set : ∀ {S : Type},  @eqv S -> @eqv (finite_set S)
:= λ {S} eqvS,
  let eq := eqv_eq eqvS in
  let s := eqv_witness eqvS in 
 {| 
     eqv_eq       := brel_set eq 
    ; eqv_witness := s :: nil 
    ; eqv_new     := λ (l : finite_set S), if brel_set eq nil l then (s :: nil) else nil
    ; eqv_data    := λ d, DATA_list (List.map (eqv_data eqvS) d)  (* need DATA_set *) 
    ; eqv_rep     := λ d, d  (* fix this? *) 
    ; eqv_ast     := Ast_eqv_set (eqv_ast eqvS)
   |}. 

