Require Import CAS.code.basic_types. 
Require Import CAS.code.ast. 
Require Import CAS.code.brel. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.   
Require Import CAS.theory.brel.eq_list.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.

Open Scope list_scope. 


Definition eqv_proofs_brel_list : ∀ (S : Type) (r : brel S), eqv_proofs S r → eqv_proofs (list S) (brel_list r) 
:= λ S r eqv, 
   {| 
     A_eqv_congruence  := brel_list_congruence S r 
                                  (A_eqv_symmetric S r eqv) 
                                  (A_eqv_transitive S r eqv) 
                                  (A_eqv_congruence S r eqv) 
   ; A_eqv_reflexive   := brel_list_reflexive S r  (A_eqv_reflexive S r eqv) 
   ; A_eqv_transitive  := brel_list_transitive S r (A_eqv_transitive S r eqv) 
   ; A_eqv_symmetric   := brel_list_symmetric S r  (A_eqv_symmetric S r eqv) 
   |}. 


Definition A_eqv_list : ∀ (S : Type),  A_eqv S -> A_eqv (list S) 
:= λ S eqvS, 
   {| 
      A_eqv_eq     := brel_list (A_eqv_eq S eqvS)
    ; A_eqv_proofs := eqv_proofs_brel_list S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS)                                                                   

    ; A_eqv_witness := nil 
    ; A_eqv_new     := λ (l : list S), (A_eqv_witness S eqvS) :: l
    ; A_eqv_not_trivial := brel_list_not_trivial S
                             (A_eqv_eq S eqvS)
                             (A_eqv_witness S eqvS)
                             (A_eqv_new S eqvS)
                             (A_eqv_symmetric S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS))
                             (A_eqv_not_trivial S eqvS)

    ; A_eqv_data   := λ l, DATA_list (List.map (A_eqv_data S eqvS) l)
    ; A_eqv_rep    := λ l, List.map (A_eqv_rep S eqvS) l
    ; A_eqv_ast    := Ast_eqv_list (A_eqv_ast S eqvS)
   |}. 

