Require Import Coq.Strings.Ascii.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.ascii.
Require Import CAS.coq.eqv.list. 


Section ACAS.

Definition A_eqv_string := A_eqv_list ascii A_eqv_ascii. 

End ACAS.

Section CAS.

Definition eqv_string := eqv_list eqv_ascii.   

End CAS.

  
