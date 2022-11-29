Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.eqv.manger_sets. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.product. 

(* for testing *)
Require Import CAS.coq.sg.manger_llex.
Require Import CAS.coq.eqv.nat. 
Require Import CAS.coq.sg.min.
Require Import CAS.coq.sg.plus.
Require Import CAS.coq.po.from_sg. 

Section Computation.


(* 
  A = type of active component
  P = type of passive component
*)   

Definition manger_product_phase_0
           {A P : Type}
           (eqA : brel A)
           (eqP : brel P)                       
           (mulA : binary_op A)
           (mulP : binary_op P) : binary_op (finite_set (A * P)) := 
  bop_lift (brel_product eqA eqP) (bop_product mulA mulP). 

(* is this a reduction over manger_product_phase_0? 
 
   r1 = uop_manger_phase_1

*)   

Definition manger_product_phase_1 
           {A P : Type}
           (eqA : brel A)
           (eqP : brel P)                       
           (addP : binary_op P)
           (mulA : binary_op A)
           (mulP : binary_op P) : binary_op (finite_set (A * P))
  := λ X Z, uop_manger_phase_1 eqA addP (manger_product_phase_0 eqA eqP mulA mulP X Z). 

(* is this really the composition of reductions? 

   r2 = uop_manger_phase_2 
*) 

Definition bop_manger_product 
           {A P : Type}
           (eqA lteA : brel A)
           (eqP : brel P)            
           (addP : binary_op P)
           (mulA : binary_op A)
           (mulP : binary_op P) : binary_op (finite_set (A * P))
  := λ X Z, @uop_manger_phase_2 A P lteA (manger_product_phase_1 eqA eqP addP mulA mulP X Z). 


End Computation.

Section Testing.

(*  A = nat * nat, P = nat *) 
   
Local Definition eqA := brel_product brel_eq_nat brel_eq_nat. 
Local Definition addA := bop_product bop_min bop_min. 
Local Definition lteA := brel_lte_left eqA addA. 
Local Definition mulA := bop_product bop_plus bop_plus. 

Local Definition eqP  := brel_eq_nat.
Local Definition addP := bop_min. 
Local Definition mulP := bop_plus.

Local Definition manger_add := bop_manger_llex eqA lteA eqP addP.
Local Definition manger_mul := bop_manger_product eqA lteA eqP addP mulA mulP.
(*
  Check manger_add.
  : binary_op (finite_set (nat * nat * nat))

  Check manger_mul.
  : binary_op (finite_set (nat * nat * nat))
 *)

Open Scope nat_scope. 

Local Definition s1 := ((1, 2), 8) :: nil.
Local Definition s2 := ((3, 5), 9) :: nil.
Local Definition s3 := ((0, 5), 9) :: nil.
Local Definition s4 := ((1, 2), 10) :: nil.
Local Definition s5 := ((1, 2), 1):: ((1, 2), 2)::((1, 2), 3) :: nil.
Compute (manger_add s1 s2). (* = (1, 2, 8) :: nil *)
Compute (manger_add s1 s3). (* = (0, 5, 9) :: (1, 2, 8) :: nil *)
Compute (manger_add s1 s4). (* = (1, 2, 8) :: nil *)
Compute (manger_add s1 s1). (* = (1, 2, 8) :: nil *)
Compute (manger_add s5 nil). (* = (1, 2, 1) :: nil *)
Compute (manger_add nil s5). (* = (1, 2, 1) :: nil *)
Compute (manger_mul s1 s2). (* = (4, 7, 17) :: nil *) 
Compute (manger_mul s2 s5). (* = (4, 7, 10) :: nil *)
Compute (manger_add (manger_mul s5 s1) (manger_mul s5 s3)). (* (1, 7, 10) :: (2, 4, 9) :: nil *) 
Compute (manger_mul s5 (manger_add s1 s3)).                 (* (2, 4, 9) :: (1, 7, 10) :: nil *) 

End Testing.

Section Theory.

End Theory.  


