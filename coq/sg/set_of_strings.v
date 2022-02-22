Require Import CAS.coq.eqv.string.
Require Import CAS.coq.sg.structures. 
Require Import CAS.coq.sg.union.

Definition A_sg_set_of_string_with_union := A_sg_union A_eqv_string. 

Definition sg_set_of_string_with_union := sg_union eqv_string. 

Definition mcas_sg_set_of_string_with_union := sg_classify _ (MCAS_sg sg_set_of_string_with_union).  

