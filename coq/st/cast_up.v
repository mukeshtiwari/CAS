Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast. 
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures. 
Require Import CAS.coq.tr.structures.
Require Import CAS.coq.st.structures.
Require Import CAS.coq.st.properties.
Require Import CAS.coq.sg.cast_up.




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
          --------------------------------------------------------------
          |                |                 |                  |
      A_slt_CS    A_slt_zero_is_ltr_ann     A_slt_CI     A_left_pre_semiring

*)  
Section Proofs.

  Context 
    {L S : Type}
    (r : brel S)
    (b : binary_op S)
    (s : S)
    (f : S -> S)
    (Pf : properties.brel_not_trivial S r f)
    (eqvS : eqv_proofs S r)
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

 
  Lemma sg_CS_to_sg_proof (A : sg_CS_proofs S r b) : sg_proofs S r b.
  Proof.
    pose proof (A_sg_C_proofs_from_sg_CS_proofs S r b s f Pf eqvS A) 
    as sg_C_proof.
    exact (A_sg_proofs_from_sg_C_proofs S r b s f Pf eqvS sg_C_proof).
  Defined.
    

  Lemma sg_CI_to_sg_proof (A : sg_CI_proofs S r b) : sg_proofs S r b.
  Proof.
    pose proof (A_sg_C_proofs_from_sg_CI_proofs S r b s f Pf eqvS A) 
    as sg_C_proof.
    exact (A_sg_proofs_from_sg_C_proofs S r b s f Pf eqvS sg_C_proof).
  Defined.

  Lemma sg_C_to_sg_proof (A : sg_C_proofs S r b) : sg_proofs S r b.
  Proof.
    exact (A_sg_proofs_from_sg_C_proofs S r b s f Pf eqvS A).
  Defined.

 
End Proofs.    


Section ACAS.
  

  Definition cast_slt_proof_to_slt_proof  {L S : Type} 
    (r : brel S) (add : binary_op S)
    (ltr : ltr_type L S) (A : slt_proofs r add ltr) :
    slt_proofs r add ltr := A. 


  Definition cast_left_dioid_proof_to_slt_proof {L S : Type} 
    (r : brel S) (add : binary_op S)
    (ltr : ltr_type L S)
    (A : left_dioid_proofs r add ltr) : slt_proofs r add ltr :=
    {|
        A_slt_distributive_d := inl (A_left_dioid_distributive r add ltr A)
      ; A_slt_absorptive_d := inl (A_left_dioid_absorptive r add ltr A)
      ; A_slt_strictly_absorptive_d := A_left_dioid_strictly_absorptive_d r add ltr A   
    |}.

  

  Definition cast_left_semiring_proof_to_slt_proof 
    {L S : Type} 
    (r : brel S) (add : binary_op S)
    (ltr : ltr_type L S)
    (A : left_semiring_proofs r add ltr) : slt_proofs r add ltr :=
    {|
        A_slt_distributive_d := inl (A_left_semiring_distributive r add ltr A)
      ; A_slt_absorptive_d := inr (A_left_semiring_not_absorptive r add ltr A) 
      ; A_slt_strictly_absorptive_d := 
          semiring_not_strictly_absorptive r add ltr A
    |}.

  
  Definition cast_A_left_dioid_to_A_left_dioid  {L S : Type} 
    (A : @A_left_dioid L S) : A_left_dioid := A.

  Definition cast_A_selective_left_dioid_to_A_selective_left_dioid 
    {L S : Type} (A : @A_selective_left_dioid L S) : 
    @A_selective_left_dioid L S := A.


  Definition cast_A_selective_left_pre_dioid_to_A_selective_left_pre_dioid
    {L S : Type} (A : @A_selective_left_pre_dioid L S) :
    @A_selective_left_pre_dioid L S := A.
    

  Definition cast_A_selective_left_dioid_to_A_selective_left_pre_dioid 
    {L S : Type} (A : @A_selective_left_dioid L S) : @A_selective_left_pre_dioid L S :=
    {|
      A_selective_left_pre_dioid_carrier := A_selective_left_dioid_carrier A 
    ; A_selective_left_pre_dioid_label := A_selective_left_dioid_label A 
    ; A_selective_left_pre_dioid_plus := A_selective_left_dioid_plus A                                            
    ; A_selective_left_pre_dioid_trans := A_selective_left_dioid_trans A 
    ; A_selective_left_pre_dioid_plus_proofs := A_selective_left_dioid_plus_proofs A
    ; A_selective_left_pre_dioid_trans_proofs := A_selective_left_dioid_trans_proofs A
    ; A_selective_left_pre_dioid_exists_plus_ann := A_selective_left_dioid_exists_plus_ann A                                
    ; A_selective_left_pre_dioid_id_ann_proofs_d := 
      SLT_Id_Ann_Proof_Equal _ _ _ (A_selective_left_dioid_id_ann_proofs A)                
    ; A_selective_left_pre_dioid_proofs := A_selective_left_dioid_proofs A                                
    ; A_selective_left_pre_dioid_ast := A_selective_left_dioid_ast A 
  |}.
  

  Definition cast_A_left_selective_semiring_to_A_left_selective_semiring
    {L S : Type}  (A : @A_left_selective_semiring L S : Type) : 
    @A_left_selective_semiring L S := A.

  
  Definition cast_A_left_idempotent_semiring_to_A_left_idempotent_semiring 
    {L S : Type}  (A : @A_left_idempotent_semiring L S) : 
    @A_left_idempotent_semiring L S := A.


  Definition cast_A_left_semiring_to_A_left_semiring 
    {L S : Type} (A : @A_left_semiring L S) : @A_left_semiring L S := A.


  Definition cast_A_left_semiring_to_A_left_pre_semiring
    {L S : Type} (A : @A_left_semiring L S) : @A_left_pre_semiring L S :=
    {|
      A_left_pre_semiring_carrier := A_left_semiring_carrier A 
    ; A_left_pre_semiring_label := A_left_semiring_label A
    ; A_left_pre_semiring_plus := A_left_semiring_plus A                                               
    ; A_left_pre_semiring_trans := A_left_semiring_trans A 
    ; A_left_pre_semiring_plus_proofs := A_left_semiring_plus_proofs A                                
    ; A_left_pre_semiring_trans_proofs := A_left_semiring_trans_proofs A 
    ; A_left_pre_semiring_exists_plus_ann_d := A_left_semiring_exists_plus_ann_d A                            
    ; A_left_pre_semiring_id_ann_proofs_d  :=
        SLT_Id_Ann_Proof_Equal _ _ _ (A_left_semiring_id_ann_proofs A)
    ; A_left_pre_semiring_proofs := A_left_semiring_proofs A 
    ; A_left_pre_semiring_ast  := A_left_semiring_ast A 
  |}.
  

  Definition cast_A_left_pre_semiring_to_A_left_pre_semiring
    {L S : Type} (A : @A_left_pre_semiring L S) : 
    @A_left_pre_semiring L S := A.

  Definition cast_A_left_pre_semiring_to_A_slt 
    {L S : Type} (A : @A_left_pre_semiring L S) : 
    @A_slt L S :=
    {|
        A_slt_carrier := A_left_pre_semiring_carrier A
      ; A_slt_label := A_left_pre_semiring_label A
      ; A_slt_plus := A_left_pre_semiring_plus A                                               
      ; A_slt_trans := A_left_pre_semiring_trans A 
      ; A_slt_plus_proofs := sg_C_to_sg_proof 
          (A_eqv_eq S (A_left_pre_semiring_carrier A))
          (A_left_pre_semiring_plus A)
          (A_eqv_witness _ (A_left_pre_semiring_carrier A)) 
          (A_eqv_new _ (A_left_pre_semiring_carrier A)) 
          (A_eqv_not_trivial _ (A_left_pre_semiring_carrier A))
          (A_eqv_proofs _ (A_left_pre_semiring_carrier A))
          (A_left_pre_semiring_plus_proofs A)                     
      ; A_slt_trans_proofs := A_left_pre_semiring_trans_proofs A 
      ; A_slt_exists_plus_ann_d :=  A_left_pre_semiring_exists_plus_ann_d A                                
      ; A_slt_id_ann_proofs_d  := A_left_pre_semiring_id_ann_proofs_d A                                              
      ; A_slt_proofs := cast_left_semiring_proof_to_slt_proof 
        (A_eqv_eq S (A_left_pre_semiring_carrier A))
        (A_left_pre_semiring_plus A)
        (A_left_pre_semiring_trans A) 
        (A_left_pre_semiring_proofs A)                               
      ; A_slt_ast := A_left_pre_semiring_ast A 
    |}.


  Definition cast_A_slt_CS_to_A_slt_CS {L S : Type} 
    (A : @A_slt_CS L S) : @A_slt_CS L S := A.


  Definition cast_A_selective_left_pre_dioid_to_A_slt_CS 
    {L S : Type} (A : @A_selective_left_pre_dioid L S) : @A_slt_CS L S :=
    {|
        A_slt_CS_carrier  := A_selective_left_pre_dioid_carrier A 
      ; A_slt_CS_label := A_selective_left_pre_dioid_label A
      ; A_slt_CS_plus := A_selective_left_pre_dioid_plus A                                               
      ; A_slt_CS_trans := A_selective_left_pre_dioid_trans A 
      ; A_slt_CS_plus_proofs := A_selective_left_pre_dioid_plus_proofs A                        
      ; A_slt_CS_trans_proofs := A_selective_left_pre_dioid_trans_proofs A
      ; A_slt_CS_exists_plus_ann_d := inl (A_selective_left_pre_dioid_exists_plus_ann A)                                
      ; A_slt_CS_id_ann_proofs_d  := A_selective_left_pre_dioid_id_ann_proofs_d A                                         
      ; A_slt_CS_proofs := cast_left_dioid_proof_to_slt_proof 
          (A_eqv_eq S (A_selective_left_pre_dioid_carrier A))
          (A_selective_left_pre_dioid_plus A)
          (A_selective_left_pre_dioid_trans A) 
          (A_selective_left_pre_dioid_proofs A)                           
      ; A_slt_CS_ast := A_selective_left_pre_dioid_ast A
    |}.


  Definition cast_A_selective_left_dioid_to_A_slt_CS 
    {L S : Type} (A : @A_selective_left_dioid L S) : @A_slt_CS L S :=
    let As :=  cast_A_selective_left_dioid_to_A_selective_left_pre_dioid A in 
    cast_A_selective_left_pre_dioid_to_A_slt_CS As. 


 
  

  Definition cast_A_left_selective_semiring_to_A_slt_CS 
    {L S : Type} (A : @A_left_selective_semiring L S) : @A_slt_CS L S :=
    {|
        A_slt_CS_carrier  := A_left_selective_semiring_carrier A
      ; A_slt_CS_label := A_left_selective_semiring_label A 
      ; A_slt_CS_plus := A_left_selective_semiring_plus A                                              
      ; A_slt_CS_trans := A_left_selective_semiring_trans A 
      ; A_slt_CS_plus_proofs := A_left_selective_semiring_plus_proofs A                        
      ; A_slt_CS_trans_proofs := A_left_selective_semiring_trans_proofs A
      ; A_slt_CS_exists_plus_ann_d := A_left_selective_semiring_exists_plus_ann_d A                               
      ; A_slt_CS_id_ann_proofs_d  := 
          SLT_Id_Ann_Proof_Equal _ _ _ (A_left_selective_semiring_id_ann_proofs A)                                         
      ; A_slt_CS_proofs := cast_left_semiring_proof_to_slt_proof 
          (A_eqv_eq S (A_left_selective_semiring_carrier A))
          (A_left_selective_semiring_plus A)
          (A_left_selective_semiring_trans A) 
          (A_left_selective_semiring_proofs A)                           
      ; A_slt_CS_ast := A_left_selective_semiring_ast A
    |}.




  Definition cast_A_slt_CI_to_A_slt_CI {L S : Type} 
    (A : @A_slt_CI L S) : @A_slt_CI L S := A.

  Definition cast_A_left_dioid_to_A_slt_CI 
    {L S : Type} (A : @A_left_dioid L S) : @A_slt_CI L S :=
    {|
        A_slt_CI_carrier := A_left_dioid_carrier A
      ; A_slt_CI_label := A_left_dioid_label A 
      ; A_slt_CI_plus := A_left_dioid_plus A                                              
      ; A_slt_CI_trans := A_left_dioid_trans A
      ; A_slt_CI_plus_proofs  := A_left_dioid_plus_proofs A                       
      ; A_slt_CI_trans_proofs := A_left_dioid_trans_proofs A
      ; A_slt_CI_exists_plus_ann_d := inl (A_left_dioid_exists_plus_ann A)                               
      ; A_slt_CI_id_ann_proofs_d :=
          SLT_Id_Ann_Proof_Equal _ _ _ (A_left_dioid_id_ann_proofs A)                                         
      ; A_slt_CI_proofs := cast_left_dioid_proof_to_slt_proof 
          (A_eqv_eq S (A_left_dioid_carrier A))
          (A_left_dioid_plus A)
          (A_left_dioid_trans A) 
          (A_left_dioid_proofs A)                                   
      ; A_slt_CI_ast := A_left_dioid_ast A 
    |}. 
  

  Definition cast_A_left_idempotent_semiring_to_A_slt_CI 
    {L S : Type} (A : @A_left_idempotent_semiring L S) : @A_slt_CI L S :=
    {|
        A_slt_CI_carrier  := A_left_idempotent_semiring_carrier A
      ; A_slt_CI_label := A_left_idempotent_semiring_label A 
      ; A_slt_CI_plus := A_left_idempotent_semiring_plus A                                              
      ; A_slt_CI_trans := A_left_idempotent_semiring_trans A
      ; A_slt_CI_plus_proofs  := A_left_idempotent_semiring_plus_proofs A                       
      ; A_slt_CI_trans_proofs := A_left_idempotent_semiring_trans_proofs A
      ; A_slt_CI_exists_plus_ann_d := A_left_idempotent_semiring_exists_plus_ann_d A                              
      ; A_slt_CI_id_ann_proofs_d :=
          SLT_Id_Ann_Proof_Equal _ _ _ (A_left_idempotent_semiring_id_ann_proofs A)                                         
      ; A_slt_CI_proofs := cast_left_semiring_proof_to_slt_proof 
          (A_eqv_eq S (A_left_idempotent_semiring_carrier A))
          (A_left_idempotent_semiring_plus A)
          (A_left_idempotent_semiring_trans A) 
          (A_left_idempotent_semiring_proofs A)                                   
      ; A_slt_CI_ast := A_left_idempotent_semiring_ast A 
    |}. 
    

  Definition cast_A_slt_zero_is_ltr_ann_to_A_slt_zero_is_ltr_ann 
    {L S : Type} (A : @A_slt_zero_is_ltr_ann L S) : 
    @A_slt_zero_is_ltr_ann L S := A. 


  Definition cast_A_selective_left_dioid_to_A_slt_zero_is_ltr_ann 
    {L S : Type}  (A : @A_selective_left_dioid L S) : 
    @A_slt_zero_is_ltr_ann L S :=
    {|
        A_slt_zero_is_ltr_ann_carrier := A_selective_left_dioid_carrier A 
      ; A_slt_zero_is_ltr_ann_label := A_selective_left_dioid_label A
      ; A_slt_zero_is_ltr_ann_plus  := A_selective_left_dioid_plus A 
      ; A_slt_zero_is_ltr_ann_trans := A_selective_left_dioid_trans A 
      ; A_slt_zero_is_ltr_ann_plus_proofs  := sg_CS_to_sg_proof 
          (A_eqv_eq S (A_selective_left_dioid_carrier A))
          (A_selective_left_dioid_plus A)  
          (A_eqv_witness _ (A_selective_left_dioid_carrier A)) 
          (A_eqv_new _ (A_selective_left_dioid_carrier A)) 
          (A_eqv_not_trivial _ (A_selective_left_dioid_carrier A)) 
          (A_eqv_proofs _ (A_selective_left_dioid_carrier A))
          (A_selective_left_dioid_plus_proofs A)                 
      ; A_slt_zero_is_ltr_ann_trans_proofs := A_selective_left_dioid_trans_proofs A 
      ; A_slt_zero_is_ltr_ann_exists_plus_ann_d := inl (A_selective_left_dioid_exists_plus_ann A)                                
      ; A_slt_zero_is_ltr_ann_id_ann_proofs  := A_selective_left_dioid_id_ann_proofs A  
      ; A_slt_zero_is_ltr_ann_proofs :=  cast_left_dioid_proof_to_slt_proof 
        (A_eqv_eq S (A_selective_left_dioid_carrier A))
        (A_selective_left_dioid_plus A)
        (A_selective_left_dioid_trans A) 
        (A_selective_left_dioid_proofs A)                                  
      ; A_slt_zero_is_ltr_ann_ast := A_selective_left_dioid_ast A 
    |}.



   

  Definition cast_A_left_dioid_to_A_slt_zero_is_ltr_ann   
    {L S : Type} (A : @A_left_dioid L S) : 
    @A_slt_zero_is_ltr_ann L S :=
    {|
        A_slt_zero_is_ltr_ann_carrier := A_left_dioid_carrier A 
      ; A_slt_zero_is_ltr_ann_label := A_left_dioid_label A
      ; A_slt_zero_is_ltr_ann_plus  := A_left_dioid_plus A 
      ; A_slt_zero_is_ltr_ann_trans := A_left_dioid_trans A 
      ; A_slt_zero_is_ltr_ann_plus_proofs  := sg_CI_to_sg_proof 
        (A_eqv_eq S (A_left_dioid_carrier A))
        (A_left_dioid_plus A) 
        (A_eqv_witness _ (A_left_dioid_carrier A)) 
        (A_eqv_new _ (A_left_dioid_carrier A)) 
        (A_eqv_not_trivial _ (A_left_dioid_carrier A)) 
        (A_eqv_proofs _ (A_left_dioid_carrier A))
        (A_left_dioid_plus_proofs A)                              
      ; A_slt_zero_is_ltr_ann_trans_proofs := A_left_dioid_trans_proofs A 
      ; A_slt_zero_is_ltr_ann_exists_plus_ann_d := inl (A_left_dioid_exists_plus_ann A)                                
      ; A_slt_zero_is_ltr_ann_id_ann_proofs  := A_left_dioid_id_ann_proofs A  
      ; A_slt_zero_is_ltr_ann_proofs :=  cast_left_dioid_proof_to_slt_proof 
        (A_eqv_eq S (A_left_dioid_carrier A))
        (A_left_dioid_plus A)
        (A_left_dioid_trans A) 
        (A_left_dioid_proofs A)                                  
      ; A_slt_zero_is_ltr_ann_ast := A_left_dioid_ast A 
    |}.

      

  Definition cast_A_left_semiring_to_A_slt_zero_is_ltr_ann   
    {L S : Type} (A : @A_left_semiring L S) : 
    @A_slt_zero_is_ltr_ann L S :=
  {|
      A_slt_zero_is_ltr_ann_carrier := A_left_semiring_carrier A 
    ; A_slt_zero_is_ltr_ann_label := A_left_semiring_label A
    ; A_slt_zero_is_ltr_ann_plus  := A_left_semiring_plus A 
    ; A_slt_zero_is_ltr_ann_trans := A_left_semiring_trans A 
    ; A_slt_zero_is_ltr_ann_plus_proofs  := A_sg_proofs_from_sg_C_proofs 
          S (A_eqv_eq S (A_left_semiring_carrier A))
          (A_left_semiring_plus A)
          (A_eqv_witness _ (A_left_semiring_carrier A)) 
          (A_eqv_new _ (A_left_semiring_carrier A)) 
          (A_eqv_not_trivial _ (A_left_semiring_carrier A)) 
          (A_eqv_proofs S (A_left_semiring_carrier A))
          (A_left_semiring_plus_proofs A)                          
    ; A_slt_zero_is_ltr_ann_trans_proofs := A_left_semiring_trans_proofs A 
    ; A_slt_zero_is_ltr_ann_exists_plus_ann_d := A_left_semiring_exists_plus_ann_d A                                 
    ; A_slt_zero_is_ltr_ann_id_ann_proofs  := A_left_semiring_id_ann_proofs A  
    ; A_slt_zero_is_ltr_ann_proofs :=  cast_left_semiring_proof_to_slt_proof 
      (A_eqv_eq S (A_left_semiring_carrier A))
      (A_left_semiring_plus A)
      (A_left_semiring_trans A) 
      (A_left_semiring_proofs A)                                  
    ; A_slt_zero_is_ltr_ann_ast := A_left_semiring_ast A 
  
  |}.
  

  Definition cast_A_left_idempotent_semiring_to_A_slt_zero_is_ltr_ann 
    {L S : Type} (A : @A_left_idempotent_semiring L S) : 
    @A_slt_zero_is_ltr_ann L S :=
    ({|

        A_slt_zero_is_ltr_ann_carrier := A_left_idempotent_semiring_carrier A 
      ; A_slt_zero_is_ltr_ann_label := A_left_idempotent_semiring_label A
      ; A_slt_zero_is_ltr_ann_plus  := A_left_idempotent_semiring_plus A 
      ; A_slt_zero_is_ltr_ann_trans := A_left_idempotent_semiring_trans A 
      ; A_slt_zero_is_ltr_ann_plus_proofs  := sg_CI_to_sg_proof 
          (A_eqv_eq S (A_left_idempotent_semiring_carrier A))
          (A_left_idempotent_semiring_plus A) 
          (A_eqv_witness _ (A_left_idempotent_semiring_carrier A)) 
          (A_eqv_new _ (A_left_idempotent_semiring_carrier A)) 
          (A_eqv_not_trivial _ (A_left_idempotent_semiring_carrier A)) 
          (A_eqv_proofs _ (A_left_idempotent_semiring_carrier A))
          (A_left_idempotent_semiring_plus_proofs A)              
      ; A_slt_zero_is_ltr_ann_trans_proofs := A_left_idempotent_semiring_trans_proofs A 
      ; A_slt_zero_is_ltr_ann_exists_plus_ann_d := A_left_idempotent_semiring_exists_plus_ann_d A
      ; A_slt_zero_is_ltr_ann_id_ann_proofs  := A_left_idempotent_semiring_id_ann_proofs A  
      ; A_slt_zero_is_ltr_ann_proofs :=  cast_left_semiring_proof_to_slt_proof 
        (A_eqv_eq S (A_left_idempotent_semiring_carrier A))
        (A_left_idempotent_semiring_plus A)
        (A_left_idempotent_semiring_trans A) 
        (A_left_idempotent_semiring_proofs A)
      ; A_slt_zero_is_ltr_ann_ast := A_left_idempotent_semiring_ast A 
    |}).


  
  Definition cast_A_slt_CS_to_A_slt 
    {L S : Type} (A : @A_slt_CS L S) : 
    @A_slt L S :=
    {|
          A_slt_carrier := A_slt_CS_carrier A
        ; A_slt_label := A_slt_CS_label A
        ; A_slt_plus := A_slt_CS_plus A                                               
        ; A_slt_trans := A_slt_CS_trans A 
        ; A_slt_plus_proofs := sg_CS_to_sg_proof 
            (A_eqv_eq S (A_slt_CS_carrier A))
            (A_slt_CS_plus A)
            (A_eqv_witness _ (A_slt_CS_carrier A)) 
            (A_eqv_new _ (A_slt_CS_carrier A)) 
            (A_eqv_not_trivial _ (A_slt_CS_carrier A))
            (A_eqv_proofs _ (A_slt_CS_carrier A))
            (A_slt_CS_plus_proofs A)                        
        ; A_slt_trans_proofs := A_slt_CS_trans_proofs A 
        ; A_slt_exists_plus_ann_d :=  A_slt_CS_exists_plus_ann_d A                                
        ; A_slt_id_ann_proofs_d  := A_slt_CS_id_ann_proofs_d A                                              
        ; A_slt_proofs := A_slt_CS_proofs A                                 
        ; A_slt_ast := A_slt_CS_ast A 
    |}.
    
    
  Definition cast_A_slt_zero_is_ltr_ann_to_A_slt 
    {L S : Type} 
    (A : @A_slt_zero_is_ltr_ann L S)  : @A_slt L S :=
    {|
        A_slt_carrier := A_slt_zero_is_ltr_ann_carrier A
      ; A_slt_label := A_slt_zero_is_ltr_ann_label A
      ; A_slt_plus := A_slt_zero_is_ltr_ann_plus A                                               
      ; A_slt_trans := A_slt_zero_is_ltr_ann_trans A 
      ; A_slt_plus_proofs := A_slt_zero_is_ltr_ann_plus_proofs A                       
      ; A_slt_trans_proofs := A_slt_zero_is_ltr_ann_trans_proofs A 
      ; A_slt_exists_plus_ann_d :=  A_slt_zero_is_ltr_ann_exists_plus_ann_d A                                
      ; A_slt_id_ann_proofs_d  := 
          SLT_Id_Ann_Proof_Equal _ _ _ (A_slt_zero_is_ltr_ann_id_ann_proofs A)                                              
      ; A_slt_proofs := A_slt_zero_is_ltr_ann_proofs A                                 
      ; A_slt_ast := A_slt_zero_is_ltr_ann_ast A
    |}.

  
  Definition cast_A_slt_CI_to_A_slt 
    {L S : Type} (A : @A_slt_CI L S) : 
    @A_slt L S :=
    {|
          A_slt_carrier := A_slt_CI_carrier A
        ; A_slt_label := A_slt_CI_label A
        ; A_slt_plus := A_slt_CI_plus A                                               
        ; A_slt_trans := A_slt_CI_trans A 
        ; A_slt_plus_proofs := sg_CI_to_sg_proof 
          (A_eqv_eq S (A_slt_CI_carrier A))
          (A_slt_CI_plus A) 
          (A_eqv_witness _ (A_slt_CI_carrier A)) 
          (A_eqv_new _ (A_slt_CI_carrier A)) 
          (A_eqv_not_trivial _ (A_slt_CI_carrier A))
          (A_eqv_proofs _ (A_slt_CI_carrier A))
          (A_slt_CI_plus_proofs A)                              
        ; A_slt_trans_proofs := A_slt_CI_trans_proofs A 
        ; A_slt_exists_plus_ann_d :=  A_slt_CI_exists_plus_ann_d A                                
        ; A_slt_id_ann_proofs_d  := A_slt_CI_id_ann_proofs_d A                                              
        ; A_slt_proofs := A_slt_CI_proofs A                                 
        ; A_slt_ast := A_slt_CI_ast A 
    |}.


  Definition cast_A_selective_left_pre_dioid_to_A_slt 
    {L S : Type} 
    (A : @A_selective_left_pre_dioid L S) : @A_slt L S :=
    let As := @cast_A_selective_left_pre_dioid_to_A_slt_CS L S A in 
    @cast_A_slt_CS_to_A_slt L S As.

  


  Definition cast_A_left_selective_semiring_to_A_slt
    {L S : Type}  
    (A : @A_left_selective_semiring L S) : @A_slt L S :=
    let As := @cast_A_left_selective_semiring_to_A_slt_CS L S A in 
    @cast_A_slt_CS_to_A_slt L S As.


  Definition cast_A_left_dioid_to_A_slt 
    {L S : Type}  
    (A : @A_left_dioid L S) : @A_slt L S :=
    let As := @cast_A_left_dioid_to_A_slt_CI L S A in
    @cast_A_slt_CI_to_A_slt L S As.


  Definition cast_A_left_idempotent_semiring_to_A_slt 
    {L S : Type} 
    (A : @A_left_idempotent_semiring L S) : @A_slt L S :=
    let As := @cast_A_left_idempotent_semiring_to_A_slt_CI L S A in 
    @cast_A_slt_CI_to_A_slt L S As.


  Definition cast_A_selective_left_dioid_to_A_slt
    {L S : Type} 
    (A : @A_selective_left_dioid L S)  : @A_slt L S :=
    let As := @cast_A_selective_left_dioid_to_A_slt_zero_is_ltr_ann L S A in 
    @cast_A_slt_zero_is_ltr_ann_to_A_slt L S As.


  Definition cast_A_left_semiring_to_A_slt 
    {L S : Type} (A : @A_left_semiring L S) : @A_slt L S  :=
    let As := @cast_A_left_semiring_to_A_slt_zero_is_ltr_ann L S A in 
    @cast_A_slt_zero_is_ltr_ann_to_A_slt L S As.


    
End ACAS.


Section AMCAS.

  From Coq Require Import List String.
  Local Open Scope string_scope.
  Import ListNotations.
  

  (* For the moment, there is nothing below the left_dioid 
    so most of the cases are error, except the left_dioid
    itself where we simply call an identity function. *)
  Definition cast_A_slt_mcas_upto_A_left_dioid 
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_left_dioid"]
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_left_dioid"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_left_dioid"]
    | A_SLT_Zero_Is_Ltr_Ann slt => 
        A_SLT_Error ["Can not cast up A_slt_zero_is_ltr_ann to A_left_dioid"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_left_dioid"]
    | A_SLT_Dioid slt => 
        A_SLT_Dioid (cast_A_left_dioid_to_A_left_dioid slt) (* identity function *)
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_left_dioid"]
    | A_SLT_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_semiring to A_left_dioid"]
    | A_SLT_Selective_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_dioid to A_left_dioid"]
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_selective_semiring to A_left_dioid"]
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_idempotent_semiring to A_left_dioid"]
    end.



  (* A_selective_left_dioid is also a bottom 
    structure and there is nothing below it. *)
  Definition  cast_A_slt_mcas_upto_A_selective_left_dioid 
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S  :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_selective_left_dioid"]
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_selective_left_dioid"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_selective_left_dioid"]
    | A_SLT_Zero_Is_Ltr_Ann slt => 
        A_SLT_Error ["Can not cast up A_slt_zero_is_ltr_ann to A_selective_left_dioid"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_selective_left_dioid"]
    | A_SLT_Dioid slt =>
        A_SLT_Error ["Can not cast up A_left_dioid to A_selective_left_dioid"]
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_selective_left_dioid"]
    | A_SLT_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_semiring to A_selective_left_dioid"]
    | A_SLT_Selective_Dioid slt => 
        A_SLT_Selective_Dioid (cast_A_selective_left_dioid_to_A_selective_left_dioid slt) (* identity function *)
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_selective_semiring to A_selective_left_dioid"]
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_idempotent_semiring to A_selective_left_dioid"]
    end.

  (* 
    selective_left_pre_dioid
          |
    selective_left_dioid
    The only structure below selective_left_pre_dioid is selective_left_dioid and 
    therefore we return values in these two cases and rest are errors.
  *)
  Definition cast_A_slt_mcas_upto_A_selective_left_pre_dioid
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
    match A with 
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_selective_left_pre_dioid"]
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_selective_left_pre_dioid"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_selective_left_pre_dioid"]
    | A_SLT_Zero_Is_Ltr_Ann slt => 
        A_SLT_Error ["Can not cast up A_slt_zero_is_ltr_ann to A_selective_left_pre_dioid"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_selective_left_pre_dioid"]
    | A_SLT_Dioid slt =>
        A_SLT_Error ["Can not cast up A_left_dioid to A_selective_left_pre_dioid"]
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Selective_Left_Pre_Dioid 
          (cast_A_selective_left_pre_dioid_to_A_selective_left_pre_dioid slt)
    | A_SLT_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_semiring to A_selective_left_pre_dioid"]
    | A_SLT_Selective_Dioid slt => 
        A_SLT_Selective_Left_Pre_Dioid (cast_A_selective_left_dioid_to_A_selective_left_pre_dioid slt)
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_selective_semiring to A_selective_left_pre_dioid"]
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_idempotent_semiring to A_selective_left_pre_dioid"]
    end.
   
   
  (*
    There is nothing below left_selective_semiring, so
    all the returns values are errors, except the 
    left_selective_semiring
  
  *)
  Definition cast_A_slt_mcas_upto_A_left_selective_semiring 
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
    match A with 
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_left_selective_semiring"]
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_left_selective_semiring"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_left_selective_semiring"]
    | A_SLT_Zero_Is_Ltr_Ann slt => 
        A_SLT_Error ["Can not cast up A_slt_zero_is_ltr_ann to A_left_selective_semiring"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_left_selective_semiring"]
    | A_SLT_Dioid slt =>
        A_SLT_Error ["Can not cast up A_left_dioid to A_left_selective_semiring"]
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error ["Can not cast up a A_selective_left_pre_dioid to A_left_selective_semiring"]
    | A_SLT_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_semiring to A_left_selective_semiring"]
    | A_SLT_Selective_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_dioid to A_left_selective_semiring"]
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Selective_Semiring (cast_A_left_selective_semiring_to_A_left_selective_semiring slt)
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_idempotent_semiring A_left_selective_semiring"]
    end.



  (*
     A_left_idempotent_semiring is a structure at the bottom,
     so all cases are error, except the  A_left_idempotent_semiring case itself
  *)
  Definition cast_A_slt_mcas_upto_A_left_idempotent_semiring 
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_left_idempotent_semiring"]
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_left_idempotent_semiring"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_left_idempotent_semiring"]
    | A_SLT_Zero_Is_Ltr_Ann slt => 
        A_SLT_Error ["Can not cast up A_slt_zero_is_ltr_ann to A_left_idempotent_semiring"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_left_idempotent_semiring"]
    | A_SLT_Dioid slt =>
        A_SLT_Error ["Can not cast up A_left_dioid to A_left_idempotent_semiring"]
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_left_idempotent_semiring"]
    | A_SLT_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_semiring to A_left_idempotent_semiring"]
    | A_SLT_Selective_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_dioid to A_left_idempotent_semiring"]
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Error ["Can not cast up A_selective_semiring to A_left_idempotent_semiring"]
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Idempotent_Semiring 
          (cast_A_left_idempotent_semiring_to_A_left_idempotent_semiring slt)
    end.

    

  (*
    A_left_semiring is a bottom structure, so all cases are 
    error, except the left_semiring itself. 
  *)
  Definition cast_A_slt_mcas_upto_A_left_semiring 
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_left_semiring"]
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_left_semiring"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_left_semiring"]
    | A_SLT_Zero_Is_Ltr_Ann slt => 
        A_SLT_Error ["Can not cast up A_slt_zero_is_ltr_ann to A_left_semiring"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_left_semiring"]
    | A_SLT_Dioid slt =>
        A_SLT_Error ["Can not cast up A_left_dioid to A_left_semiring"]
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_left_semiring"]
    | A_SLT_Semiring slt => 
        A_SLT_Semiring (cast_A_left_semiring_to_A_left_semiring slt)
    | A_SLT_Selective_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_dioid to A_left_semiring"]
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_selective_semiring to A_left_semiring"]
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_idempotent_semiring to A_left_semiring"]
    end.

   
  (*
      left_pre_semiring
          |
      left_semiring

      There is one structure, A_left_semring, below A_left_pre_semiring
      so these structures can be cast up to A_left_pre_semring. All 
      cases are error, except these two.   
  
  *)   

  Definition cast_A_slt_mcas_upto_A_left_pre_semiring   
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
    match A with 
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_left_pre_semring"]
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_left_pre_semring"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_left_pre_semring"]
    | A_SLT_Zero_Is_Ltr_Ann slt => 
        A_SLT_Error ["Can not cast up A_slt_zero_is_ltr_ann to A_left_pre_semring"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Left_Pre_Semiring 
          (cast_A_left_pre_semiring_to_A_left_pre_semiring slt)
    | A_SLT_Dioid slt =>
        A_SLT_Error ["Can not cast up A_left_dioid to A_left_pre_semring"]
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_left_pre_semring"]
    | A_SLT_Semiring slt => 
        A_SLT_Left_Pre_Semiring 
          (cast_A_left_semiring_to_A_left_pre_semiring slt)
    | A_SLT_Selective_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_dioid to A_left_pre_semring"]
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_selective_semiring to A_left_pre_semring"]
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_idempotent_semiring to A_left_pre_semring"]
    end.

    

  (*
                        A_slt_CS 
                          | 
    ---------------------------------------------------------- 
                 |                              |            
    A_selective_left_pre_dioid        A_left_selective_semiring  


    
  *)
  Definition cast_A_slt_mcas_upto_A_slt_CS {L S : Type}
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S  :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_slt_CS"]
    | A_SLT_CS slt => 
        A_SLT_CS (cast_A_slt_CS_to_A_slt_CS slt)
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_slt_CS"]
    | A_SLT_Zero_Is_Ltr_Ann slt => 
        A_SLT_Error ["Can not cast up A_slt_zero_is_ltr_ann to A_slt_CS"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_slt_CS"]
    | A_SLT_Dioid slt =>
        A_SLT_Error ["Can not cast up A_left_dioid to A_slt_CS"]
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_CS (cast_A_selective_left_pre_dioid_to_A_slt_CS slt)
    | A_SLT_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_semiring to A_slt_CS"]
    | A_SLT_Selective_Dioid slt =>    
        A_SLT_CS (cast_A_selective_left_dioid_to_A_slt_CS slt)
    | A_SLT_Selective_Semiring slt => 
        A_SLT_CS (cast_A_left_selective_semiring_to_A_slt_CS slt)
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_idempotent_semiring to A_slt_CS"]
    end.


  Definition cast_A_slt_mcas_upto_A_slt_CI {L S : Type}
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S  :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_SLT_CI"]
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_SLT_CI"]
    | A_SLT_CI slt => 
        A_SLT_CI (cast_A_slt_CI_to_A_slt_CI slt)
    | A_SLT_Zero_Is_Ltr_Ann slt => 
        A_SLT_Error ["Can not cast up A_slt_zero_is_ltr_ann to A_SLT_CI"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_SLT_CI"]
    | A_SLT_Dioid slt =>
        A_SLT_CI (cast_A_left_dioid_to_A_slt_CI  slt)
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_SLT_CI"]
    | A_SLT_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_semiring to A_SLT_CI"]
    | A_SLT_Selective_Dioid slt => A_SLT_Error [""]
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_selective_semiring to A_SLT_CI"]
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_CI (cast_A_left_idempotent_semiring_to_A_slt_CI  slt)
    end.

   
 
  Definition cast_A_slt_mcas_upto_A_slt_zero_is_ltr_ann
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_slt_zero_is_ltr_ann"]
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_slt_zero_is_ltr_ann"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_slt_zero_is_ltr_ann"]
    | A_SLT_Zero_Is_Ltr_Ann slt => 
        A_SLT_Zero_Is_Ltr_Ann (cast_A_slt_zero_is_ltr_ann_to_A_slt_zero_is_ltr_ann slt)
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_slt_zero_is_ltr_ann"]
    | A_SLT_Dioid slt =>
        A_SLT_Zero_Is_Ltr_Ann (cast_A_left_dioid_to_A_slt_zero_is_ltr_ann slt)
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error [""]
    | A_SLT_Semiring slt => 
        A_SLT_Zero_Is_Ltr_Ann (cast_A_left_semiring_to_A_slt_zero_is_ltr_ann slt)
    | A_SLT_Selective_Dioid slt => 
        A_SLT_Zero_Is_Ltr_Ann (cast_A_selective_left_dioid_to_A_slt_zero_is_ltr_ann slt)
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Error [""]
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Zero_Is_Ltr_Ann (cast_A_left_idempotent_semiring_to_A_slt_zero_is_ltr_ann slt)
    end.


  
  Definition cast_A_mcas_to_A_slt 
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => A
    | A_SLT_CS slt => 
        A_SLT (cast_A_slt_CS_to_A_slt slt)
    | A_SLT_CI slt => 
        A_SLT (cast_A_slt_CI_to_A_slt slt)
    | A_SLT_Zero_Is_Ltr_Ann slt => 
        A_SLT (cast_A_slt_zero_is_ltr_ann_to_A_slt slt)
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT (cast_A_left_pre_semiring_to_A_slt slt)
    | A_SLT_Dioid slt =>
        A_SLT (cast_A_left_dioid_to_A_slt slt)
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT (cast_A_selective_left_pre_dioid_to_A_slt slt)
    | A_SLT_Semiring slt => 
        A_SLT (cast_A_left_semiring_to_A_slt slt)
    | A_SLT_Selective_Dioid slt => 
        A_SLT (cast_A_selective_left_dioid_to_A_slt slt)
    | A_SLT_Selective_Semiring slt => 
        A_SLT (cast_A_left_selective_semiring_to_A_slt slt)
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT (cast_A_left_idempotent_semiring_to_A_slt slt)
    end.



End AMCAS.


Section Certs.

  Context 
    {L S : Type}
    (r : brel S)
    (b : binary_op S)
    (s : S)
    (f : S -> S).
  
  Lemma semiring_not_strictly_absorptive_cert :  
    @left_semiring_certificates L S -> 
    @check_slt_strictly_absorptive L S.
  Proof.
    intros [Al [p]].
    right. exact p.
  Defined. 

 
  Lemma sg_CS_to_sg_cert (A : @sg_CS_certificates S) : @sg_certificates S.
  Proof.
    pose proof (sg_C_certs_from_sg_CS_certs S r b s f A) 
    as sg_C_cert;
    exact (sg_certs_from_sg_C_certs S r b s f sg_C_cert).
  Defined.
    

  Lemma sg_CI_to_sg_cert (A : @sg_CI_certificates S) : @sg_certificates S.
  Proof.
    pose proof (sg_C_certs_from_sg_CI_certs S r b s f A) 
    as sg_C_cert;
    exact (sg_certs_from_sg_C_certs S r b s f sg_C_cert).
  Defined.

  Lemma sg_C_to_sg_cert (A : @sg_C_certificates S) : @sg_certificates S.
  Proof.
    exact (sg_certs_from_sg_C_certs S r b s f A).
  Defined.
 
End Certs.    


Section CAS. 

  Definition cast_slt_certificate_to_slt_certificate  {L S : Type}
    (A : @slt_certificates L S) :
    slt_certificates := A. 


  Definition cast_left_dioid_certificate_to_slt_certificate {L S : Type} 
    (A : @left_dioid_certificates L S) : @slt_certificates L S :=
    {|
        slt_distributive_d := Certify_Slt_Distributive
      ; slt_absorptive_d := Certify_Slt_Absorptive
      ; slt_strictly_absorptive_d := left_dioid_strictly_absorptive_d A   
    |}.


  Definition cast_left_semiring_certificate_to_slt_certificate 
    {L S : Type}
    (A : @left_semiring_certificates L S) : @slt_certificates L S :=
    {|
        slt_distributive_d := Certify_Slt_Distributive
      ; slt_absorptive_d := Certify_Slt_Not_Absorptive 
          (match left_semiring_not_absorptive A with 
          | Assert_Slt_Not_Absorptive p => p
          end)
      ; slt_strictly_absorptive_d := 
          semiring_not_strictly_absorptive_cert A
    |}.
    
  Definition cast_left_dioid_to_left_dioid  {L S : Type} 
    (A : @left_dioid L S) : left_dioid := A.

  Definition cast_selective_left_dioid_to_selective_left_dioid 
    {L S : Type} (A : @A_selective_left_dioid L S) : 
    @A_selective_left_dioid L S := A.


  Definition cast_selective_left_pre_dioid_to_selective_left_pre_dioid
    {L S : Type} (A : @selective_left_pre_dioid L S) :
    @selective_left_pre_dioid L S := A.

     

End CAS. 

