Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast. 
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures. 
Require Import CAS.coq.tr.structures.
Require Import CAS.coq.st.structures.
Require Import CAS.coq.st.properties.




(*

1.                A_slt_proof
                     |
             ------------------------     
            |                       |
    A_slt_dioid_proof      A_slt_semiring_proof

 2.   
                  left_dioid
                     |
                  left_dioid
 3.                
              selective_left_dioid
                      |
              selective_left_dioid   
4.
              selective_left_pre_dioid
                      |
              selective_left_dioid
5.
              left_selective_semiring
                      |
              left_selective_semiring
6.
              left_idempotent_semiring
                      |
              left_idempotent_semiring
7.
              left_semiring
                  |
              left_semiring
8.
              left_pre_semiring
                  |
              left_semiring
9.                           
                       A_slt_CS 
                          | 
    ---------------------------------------------------------- 
                 |                              |            
    A_selective_left_pre_dioid        A_left_selective_semiring
10.
                        A_slt_CI
                          |
       -------------------------------------                
      |                             |                   
  left_dioid              left_idempotent_semiring    

11.

                A_slt_zero_is_ltr_ann
    --------------------------------------------------------------------
           |                      |              |                   |
    selective_left_dioid      left_dioid     left_semiring   left_idempotent_semiring

12.    

                        A_slt
                          | 
          ------------------------------------------
          |                |                 |    
      A_slt_CS    A_slt_zero_is_ltr_ann     A_slt_CI

*)  
Section Proofs.

  Context 
    {L S : Type}
    (r : brel S)
    (add : binary_op S)
    (ltr : ltr_type L S).

  Lemma semiring_not_strictly_absorptive :  
    left_semiring_proofs r add ltr -> 
    slt_strictly_absorptive_decidable r add ltr.
  Proof.
    intros [Al [(x, y) Hx]].
    right; econstructor.
    instantiate (1 := (x, y)).
    left; exact Hx.
  Defined. (* becuase we the structure of simplify *)

End Proofs.    


Section Compute.
  
  Context 
    {L S : Type}
    (r : brel S)
    (add : binary_op S)
    (ltr : ltr_type L S).
  
  Definition cast_slt_proof_to_slt_proof (A : slt_proofs r add ltr) :
    slt_proofs r add ltr := A. 

    
  Definition cast_left_dioid_proof_to_slt_proof 
    (A : left_dioid_proofs r add ltr) : slt_proofs r add ltr :=
    {|
        A_slt_distributive_d := inl (A_left_dioid_distributive r add ltr A)
      ; A_slt_absorptive_d := inl (A_left_dioid_absorptive r add ltr A)
      ; A_slt_strictly_absorptive_d := A_left_dioid_strictly_absorptive_d r add ltr A   
    |}.

  

  Definition cast_left_semiring_proofs_to_slt_proofs 
    (A : left_semiring_proofs r add ltr) : slt_proofs r add ltr :=
  {|
        A_slt_distributive_d := inl (A_left_semiring_distributive r add ltr A)
      ; A_slt_absorptive_d := inr (A_left_semiring_not_absorptive r add ltr A) 
      ; A_slt_strictly_absorptive_d := 
          semiring_not_strictly_absorptive r add ltr A
    |}.

    
End Compute.

