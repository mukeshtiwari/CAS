Require Import CAS.code.basic_types. 
Require Import CAS.code.ast. 
Require Import CAS.code.brel. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.   
Require Import CAS.theory.brel.sum.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.

Definition eqv_proofs_sum : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T),
        eqv_proofs S rS -> eqv_proofs T rT -> eqv_proofs (S + T) (brel_sum rS rT) 
:= λ S T rS rT eqvS eqvT, 
{|
 A_eqv_congruence  := brel_sum_congruence S T rS rT 
                        (A_eqv_congruence S rS eqvS)
                        (A_eqv_congruence T rT eqvT)
; A_eqv_reflexive   := brel_sum_reflexive S T rS rT 
                        (A_eqv_reflexive S rS eqvS) 
                        (A_eqv_reflexive T rT eqvT) 
; A_eqv_transitive  := brel_sum_transitive S T rS rT  
                        (A_eqv_transitive S rS eqvS) 
                        (A_eqv_transitive T rT eqvT) 
; A_eqv_symmetric   := brel_sum_symmetric S T rS rT  
                        (A_eqv_symmetric S rS eqvS) 
                        (A_eqv_symmetric T rT eqvT) 
|}.

Definition A_eqv_sum : ∀ (S T : Type),  A_eqv S -> A_eqv T -> A_eqv (S + T) 
:= λ S T eqvS eqvT, 
   {| 
      A_eqv_eq     := brel_sum (A_eqv_eq S eqvS) (A_eqv_eq T eqvT) 
    ; A_eqv_proofs := eqv_proofs_sum S T 
                           (A_eqv_eq S eqvS) 
                           (A_eqv_eq T eqvT)
                           (A_eqv_proofs S eqvS) 
                           (A_eqv_proofs T eqvT) 

    ; A_eqv_witness := inl (A_eqv_witness S eqvS)
    ; A_eqv_new     := λ (d : S + T), match d with | inl _ => inr (A_eqv_witness T eqvT) | inr _ => inl (A_eqv_witness S eqvS) end
    ; A_eqv_not_trivial := brel_sum_not_trivial S T 
                             (A_eqv_eq S eqvS) 
                             (A_eqv_eq T eqvT)                                                
                             (A_eqv_witness S eqvS)
                             (A_eqv_witness T eqvT)                                                
    ; A_eqv_data  := λ d, (match d with inl s => DATA_inl (A_eqv_data S eqvS s) | inr t => DATA_inr (A_eqv_data T eqvT t) end)
    ; A_eqv_rep   := λ d, (match d with inl s => inl _ (A_eqv_rep S eqvS s) | inr t => inr _ (A_eqv_rep T eqvT t) end)
    ; A_eqv_ast   := Ast_eqv_sum (A_eqv_ast S eqvS, A_eqv_ast T eqvT)
   |}. 

