Require Import CAS.code.basic_types. 
Require Import CAS.code.ast. 
Require Import CAS.code.brel. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.   
Require Import CAS.theory.brel.add_constant.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.

Definition eqv_proofs_add_constant : ∀ (S : Type) (r : brel S) (c : cas_constant),
    eqv_proofs S r → eqv_proofs (with_constant S) (brel_add_constant r c) 
:= λ S r c eqv, 
   {| 
     A_eqv_congruence  := brel_add_constant_congruence S r c (A_eqv_congruence S r eqv) (A_eqv_congruence S r eqv)
   ; A_eqv_reflexive   := brel_add_constant_reflexive S r c (A_eqv_reflexive S r eqv) 
   ; A_eqv_transitive  := brel_add_constant_transitive S r c (A_eqv_transitive S r eqv) 
   ; A_eqv_symmetric   := brel_add_constant_symmetric S r c (A_eqv_symmetric S r eqv) 
   |}. 


Definition A_eqv_add_constant : ∀ (S : Type),  A_eqv S -> cas_constant -> A_eqv (with_constant S) 
:= λ S eqvS c, 
   {| 
      A_eqv_eq     := brel_add_constant (A_eqv_eq S eqvS) c
    ; A_eqv_proofs := eqv_proofs_add_constant S (A_eqv_eq S eqvS) c (A_eqv_proofs S eqvS)

    ; A_eqv_witness := inl c
    ; A_eqv_new     := λ (d : with_constant S), match d with | inl _ => inr _ (A_eqv_witness S eqvS)  | inr _ => inl S c end
    ; A_eqv_not_trivial := brel_add_constant_not_trivial S (A_eqv_eq S eqvS) c (A_eqv_witness S eqvS)

    ; A_eqv_data   := λ d, (match d with inl s => DATA_inl(DATA_string s) | inr a => DATA_inr (A_eqv_data S eqvS a) end)
    ; A_eqv_rep    := λ d, (match d with inl s => inl _ s  | inr s => inr _ (A_eqv_rep S eqvS s) end )

    ; A_eqv_ast    := Ast_eqv_add_constant (c, A_eqv_ast S eqvS)
   |}. 
