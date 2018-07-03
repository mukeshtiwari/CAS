Require Import CAS.code.basic_types. 
Require Import CAS.code.ast. 
Require Import CAS.code.brel. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.   
Require Import CAS.theory.brel.product. 
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.

Definition eqv_proofs_product : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T),
       eqv_proofs S rS -> eqv_proofs T rT -> eqv_proofs (S * T) (brel_product rS rT) 
:= λ S T rS rT eqvS eqvT, 
{|

  A_eqv_congruence  := brel_product_congruence S T rS rT rS rT 
                        (A_eqv_congruence S rS eqvS)
                        (A_eqv_congruence T rT eqvT)
; A_eqv_reflexive   := brel_product_reflexive S T rS rT 
                        (A_eqv_reflexive S rS eqvS) 
                        (A_eqv_reflexive T rT eqvT) 
; A_eqv_transitive  := brel_product_transitive S T rS rT  
                        (A_eqv_transitive S rS eqvS) 
                        (A_eqv_transitive T rT eqvT) 
; A_eqv_symmetric   := brel_product_symmetric S T rS rT  
                        (A_eqv_symmetric S rS eqvS) 
                        (A_eqv_symmetric T rT eqvT) 
|}.


Definition A_eqv_product : ∀ (S T : Type),  A_eqv S -> A_eqv T -> A_eqv (S * T) 
:= λ S T eqvS eqvT, 
   {| 
        A_eqv_eq     := brel_product (A_eqv_eq S eqvS) (A_eqv_eq T eqvT) 
      ; A_eqv_proofs := eqv_proofs_product S T
                           (A_eqv_eq S eqvS)                                           
                           (A_eqv_eq T eqvT)
                           (A_eqv_proofs S eqvS)
                           (A_eqv_proofs T eqvT) 

    ; A_eqv_witness := (A_eqv_witness S eqvS, A_eqv_witness T eqvT)
    ; A_eqv_new   := λ p, let (s, t) := p in ((A_eqv_new S eqvS) s, t)
    ; A_eqv_not_trivial := brel_product_not_trivial S T
                              (A_eqv_eq S eqvS)                                                                                               
                              (A_eqv_eq T eqvT)                                                    
                              (A_eqv_reflexive T (A_eqv_eq T eqvT) (A_eqv_proofs T eqvT))
                              (A_eqv_new S eqvS)
                              (A_eqv_not_trivial S eqvS)

    ; A_eqv_data  := λ p, DATA_pair (A_eqv_data S eqvS (fst p), A_eqv_data T eqvT (snd p))
    ; A_eqv_rep   := λ p, (A_eqv_rep S eqvS (fst p), A_eqv_rep T eqvT (snd p))

    ; A_eqv_ast   := Ast_eqv_product (A_eqv_ast _ eqvS, A_eqv_ast _ eqvT)
   |}. 

