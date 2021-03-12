Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.bop_properties. 
Close Scope nat. 
(* Interaction of multiple binary ops *) 

Definition bop_left_distributive (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) 
   := ∀ s t u : S, r (mul s (add t u)) (add (mul s t) (mul s u)) = true. 

Definition bop_not_left_distributive (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) 
(*    := {s : S & {t : S & {u : S & r (mul s (add t u)) (add (mul s t) (mul s u)) = false }}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) => r (mul s (add t u)) (add (mul s t) (mul s u)) = false end }. 

Definition bop_left_distributive_decidable (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) 
   := (bop_left_distributive S r add mul) + (bop_not_left_distributive S r add mul). 

Definition bop_right_distributive (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) 
    := ∀ s t u : S, r (mul (add t u) s) (add (mul t s) (mul u s)) = true. 

Definition bop_not_right_distributive (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S)    
(*   := {s : S & {t : S & {u : S & r (mul (add t u) s) (add (mul t s) (mul u s)) = false }}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) => r (mul (add t u) s) (add (mul t s) (mul u s)) = false end }. 

Definition bop_right_distributive_decidable (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) 
   := (bop_right_distributive S r add mul) + (bop_not_right_distributive S r add mul). 

Definition bops_id_equals_ann (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
:= { i : S & (bop_is_id S r b1 i) * (bop_is_ann S r b2 i)}. 

Definition bops_not_id_equals_ann (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
:= ∀ (s : S), (bop_not_is_id S r b1 s) + (bop_not_is_ann S r b2 s). 

Definition bops_id_equals_ann_decidable 
   (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
   := (bops_id_equals_ann S r b1 b2) + (bops_not_id_equals_ann S r b1 b2). 

(* Used? 
Definition bops_id_equals_id (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
:= { eI : bop_exists_id S r b1 & 
   { eA : bop_exists_id S r b2 & r (projT1 eI) (projT1 eA)  = true }}. 

Definition bops_not_id_equals_id (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
:=  ∀ (i a : S), bop_is_id S r b1 i -> bop_is_id S r b2 a -> r i a = false. 

Definition bops_id_equals_id_decidable 
   (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
   := (bops_id_equals_id S r b1 b2) + (bops_not_id_equals_id S r b1 b2). 

Definition bops_ann_equals_ann (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
:= { eI : bop_exists_ann S r b1 & 
   { eA : bop_exists_ann S r b2 & r (projT1 eI) (projT1 eA)  = true }}. 

Definition bops_not_ann_equals_ann (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
:=  ∀ (i a : S), bop_is_ann S r b1 i -> bop_is_ann S r b2 a -> r i a = false. 

Definition bops_ann_equals_ann_decidable 
   (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
   := (bops_ann_equals_ann S r b1 b2) + (bops_not_ann_equals_ann S r b1 b2). 
*) 


(* Absorptivity *) 

Definition bops_left_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 s t)) = true.

Definition bops_not_left_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) 
   := { z : S * S & match z with (s, t) => r s (b1 s (b2 s t)) = false end }. 

Definition bops_left_left_absorptive_decidable  (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    (bops_left_left_absorptive S r b1 b2) + (bops_not_left_left_absorptive S r b1 b2). 

Definition bops_left_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 t s)) = true.

Definition bops_not_left_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S)
   := { z : S * S & match z with (s, t) => r s (b1 s (b2 t s)) = false end }. 

Definition bops_left_right_absorptive_decidable  (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    (bops_left_right_absorptive S r b1 b2) + (bops_not_left_right_absorptive S r b1 b2). 

Definition bops_right_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 (b2 s t) s) = true.

Definition bops_not_right_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) 
   := { z : S * S & match z with (s, t) =>  r s (b1 (b2 s t) s) = false end }. 

Definition bops_right_left_absorptive_decidable  (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    (bops_right_left_absorptive S r b1 b2) + (bops_not_right_left_absorptive S r b1 b2). 

Definition bops_right_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 (b2 t s) s) = true.

Definition bops_not_right_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) 
   := { z : S * S & match z with (s, t) =>  r s (b1 (b2 t s) s) = false end }. 

Definition bops_right_right_absorptive_decidable  (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    (bops_right_right_absorptive S r b1 b2) + (bops_not_right_right_absorptive S r b1 b2). 

(*
Definition bops_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
          (bops_left_left_absorptive S r b1 b2)  * 
          (bops_left_right_absorptive S r b1 b2) * 
          (bops_right_left_absorptive S r b1 b2) * 
          (bops_right_right_absorptive S r b1 b2). 

Definition bops_not_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
          (bops_not_left_left_absorptive S r b1 b2)  + 
          (bops_not_left_right_absorptive S r b1 b2) +  
          (bops_not_right_left_absorptive S r b1 b2) + 
          (bops_not_right_right_absorptive S r b1 b2). 

Definition bops_absorptive_decidable  (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    (bops_absorptive S r b1 b2) + (bops_not_absorptive S r b1 b2). 


(* experiments *) 

Definition bops_left_left_dependent_distributive (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) 
   := ∀ s t u : S, r t (add t u) = true -> r (mul s t) (add (mul s t) (mul s u)) = true. 
*)
