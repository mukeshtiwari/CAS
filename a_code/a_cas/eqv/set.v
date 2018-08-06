Require Import CAS.code.basic_types. 
Require Import CAS.code.ast. 
Require Import CAS.code.brel. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.   
Require Import CAS.theory.brel.set.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.


Definition eqv_proofs_set : ∀ (S : Type) (r : brel S),
    eqv_proofs S r → eqv_proofs (finite_set S) (brel_set r) 
:= λ S r eqv, 
   {| 
     A_eqv_congruence  := brel_set_congruence S r (A_eqv_reflexive S r eqv) (A_eqv_symmetric S r eqv) (A_eqv_transitive S r eqv) 
   ; A_eqv_reflexive   := brel_set_reflexive S r (A_eqv_reflexive S r eqv) (A_eqv_symmetric S r eqv) 
   ; A_eqv_transitive  := brel_set_transitive S r (A_eqv_reflexive S r eqv) (A_eqv_symmetric S r eqv) (A_eqv_transitive S r eqv) 
   ; A_eqv_symmetric   := brel_set_symmetric S r 
   |}. 


Definition A_eqv_set : ∀ (S : Type),  A_eqv S -> A_eqv (finite_set S)
:= λ S eqvS,
  let eq := A_eqv_eq S eqvS in
  let s := A_eqv_witness S eqvS in 
   {| 
      A_eqv_eq     := brel_set eq 
    ; A_eqv_proofs := eqv_proofs_set S eq (A_eqv_proofs S eqvS)
    ; A_eqv_witness := s :: nil 
    ; A_eqv_new     := λ (l : finite_set S), if brel_set eq nil l then (s :: nil) else nil
    ; A_eqv_not_trivial := brel_set_not_trivial S eq s 

    ; A_eqv_data   := λ d, DATA_list (List.map (A_eqv_data S eqvS) d)  (* need DATA_set *) 
    ; A_eqv_rep    := λ d, d  (* fix this? *) 

    ; A_eqv_ast    := Ast_eqv_set (A_eqv_ast S eqvS)
   |}. 
