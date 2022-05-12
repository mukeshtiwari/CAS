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


Section Compute.



End Compute.
