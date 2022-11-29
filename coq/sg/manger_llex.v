Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.eqv.manger_sets. 

Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.lift. 

Section Computation.


(* 
  A = type of active component
  P = type of passive component
 *)

(* is this a reduction over union? 
 
   r1 = uop_manger_phase_1

*)   
Definition bop_manger_phase_1
           {A P : Type}
           (eqA : brel A)
           (eqP : brel P)                       
           (addP : binary_op P) : binary_op (finite_set (A * P))
  := λ X Z, uop_manger_phase_1 eqA addP (bop_union (brel_product eqA eqP) X Z).

(* is this really the composition of reductions? 

   r2 = uop_manger_phase_2 
*) 
Definition bop_manger_llex
           {A P : Type}
           (eqA lteA : brel A)
           (eqP : brel P)            
           (addP : binary_op P) : binary_op (finite_set (A * P))
  := λ X Z, @uop_manger_phase_2 A P lteA (bop_manger_phase_1 eqA eqP addP X Z). 

End Computation. 

Section Theory.

End Theory.   
