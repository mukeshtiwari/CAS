Require Import CAS.coq.common.compute.
Require Import CAS.coq.sg.properties. 


Section ACAS. 



Close Scope nat. 
(* Interaction of multiple binary ops *)


(* if this decidable property is added to bs, then we can get an iff rule for 
    (plus, times) ->(left_order plus, times) and olt_left_monotone. 
    First, try pushing bop_left_monotone through all bs combinators ... 
*) 
Definition bop_left_monotone (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) 
   := ∀ s t u : S, r t (add t u) = true -> r (mul s t) (add (mul s t) (mul s u)) = true. 

Definition bop_not_left_monotone (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) 
   := { z : S * (S * S) & match z with (s, (t, u)) => (r t (add t u) = true) * (r (mul s t) (add (mul s t) (mul s u)) = false) end }.


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

End ACAS. 

Section CAS.


Inductive assert_left_distributive {S : Type} := 
| Assert_Left_Distributive : @assert_left_distributive S. 

Inductive check_left_distributive {S : Type} := 
| Certify_Left_Distributive : @check_left_distributive S
| Certify_Not_Left_Distributive : (S * (S * S)) → @check_left_distributive S.

Inductive check_left_distributive_dual {S : Type} := 
| Certify_Left_Distributive_Dual : @check_left_distributive_dual S
| Certify_Not_Left_Distributive_Dual : (S * (S * S)) → @check_left_distributive_dual S. 

Inductive assert_right_distributive {S : Type} := 
| Assert_Right_Distributive : @assert_right_distributive S. 

Inductive check_right_distributive {S : Type} := 
| Certify_Right_Distributive : @check_right_distributive S
| Certify_Not_Right_Distributive : (S * (S * S)) → @check_right_distributive S.

Inductive assert_plus_id_equals_times_ann {S : Type} := 
| Assert_Plus_Id_Equals_Times_Ann : S → @assert_plus_id_equals_times_ann S. 

Inductive check_plus_id_equals_times_ann {S : Type} := 
| Certify_Plus_Id_Equals_Times_Ann : S → @check_plus_id_equals_times_ann S
| Certify_Not_Plus_Id_Equals_Times_Ann : @check_plus_id_equals_times_ann S.

Inductive assert_times_id_equals_plus_ann {S : Type} := 
| Assert_Times_Id_Equals_Plus_Ann : S → @assert_times_id_equals_plus_ann S. 

Inductive check_times_id_equals_plus_ann {S : Type} := 
| Certify_Times_Id_Equals_Plus_Ann : S → @check_times_id_equals_plus_ann S
| Certify_Not_Times_Id_Equals_Plus_Ann : @check_times_id_equals_plus_ann S.


Inductive assert_left_left_absorptive {S : Type} := 
| Assert_Left_Left_Absorptive : @assert_left_left_absorptive S.

Inductive assert_left_left_absorptive_dual {S : Type} := 
| Assert_Left_Left_Absorptive_Dual : @assert_left_left_absorptive_dual S. 


Inductive check_left_left_absorptive {S : Type} := 
| Certify_Left_Left_Absorptive : @check_left_left_absorptive S
| Certify_Not_Left_Left_Absorptive : (S * S) → @check_left_left_absorptive S.


Inductive assert_left_right_absorptive {S : Type} := 
| Assert_Left_Right_Absorptive : @assert_left_right_absorptive S. 

Inductive check_left_right_absorptive {S : Type} := 
| Certify_Left_Right_Absorptive : @check_left_right_absorptive S
| Certify_Not_Left_Right_Absorptive : (S * S) → @check_left_right_absorptive S.


Inductive assert_right_left_absorptive {S : Type} := 
| Assert_Right_Left_Absorptive : @assert_right_left_absorptive S. 

Inductive check_right_left_absorptive {S : Type} := 
| Certify_Right_Left_Absorptive : @check_right_left_absorptive S
| Certify_Not_Right_Left_Absorptive : (S * S) → @check_right_left_absorptive S.


Inductive assert_right_right_absorptive {S : Type} := 
| Assert_Right_Right_Absorptive : @assert_right_right_absorptive S. 

Inductive check_right_right_absorptive {S : Type} := 
| Certify_Right_Right_Absorptive : @check_right_right_absorptive S
| Certify_Not_Right_Right_Absorptive : (S * S) → @check_right_right_absorptive S.

End CAS.

Section Translation.

Definition p2c_left_left_absorptive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_left_left_absorptive_decidable S r b1 b2 -> @check_left_left_absorptive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Left_Left_Absorptive 
   | inr p => Certify_Not_Left_Left_Absorptive (projT1 p)                                             
   end. 


Definition p2c_left_right_absorptive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_left_right_absorptive_decidable S r b1 b2 -> @check_left_right_absorptive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Left_Right_Absorptive
   | inr p => Certify_Not_Left_Right_Absorptive (projT1 p)
   end. 


Definition p2c_right_left_absorptive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_right_left_absorptive_decidable S r b1 b2 -> @check_right_left_absorptive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Right_Left_Absorptive
   | inr p => Certify_Not_Right_Left_Absorptive (projT1 p)
   end. 


Definition p2c_right_right_absorptive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_right_right_absorptive_decidable S r b1 b2 -> @check_right_right_absorptive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Right_Right_Absorptive 
   | inr p => Certify_Not_Right_Right_Absorptive (projT1 p)
   end. 

Definition p2c_left_distributive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bop_left_distributive_decidable S r b1 b2 -> @check_left_distributive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Left_Distributive 
   | inr p => Certify_Not_Left_Distributive (projT1 p) 
   end. 

Definition p2c_right_distributive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bop_right_distributive_decidable S r b1 b2 -> @check_right_distributive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Right_Distributive
   | inr p => Certify_Not_Right_Distributive (projT1 p)
   end. 

Definition p2c_left_distributive_dual : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bop_left_distributive_decidable S r b2 b1 -> @check_left_distributive_dual S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Left_Distributive_Dual 
   | inr p => Certify_Not_Left_Distributive_Dual (projT1 p) 
   end. 

Definition p2c_plus_id_equals_times_ann_assert : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_id_equals_ann S r b1 b2 -> @assert_plus_id_equals_times_ann S 
:= λ S r b1 b2 p, Assert_Plus_Id_Equals_Times_Ann (projT1 p).


Definition p2c_plus_id_equals_times_ann : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_id_equals_ann_decidable S r b1 b2 -> @check_plus_id_equals_times_ann S 
:= λ S r b1 b2 d, 
   match d with 
   | inl p => Certify_Plus_Id_Equals_Times_Ann (projT1 p)
   | inr _ => Certify_Not_Plus_Id_Equals_Times_Ann 
   end. 


Definition p2c_times_id_equals_plus_ann_assert : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_id_equals_ann S r b2 b1 -> @assert_times_id_equals_plus_ann S
:= λ S r b1 b2 p, Assert_Times_Id_Equals_Plus_Ann (projT1 p). 

Definition p2c_times_id_equals_plus_ann : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_id_equals_ann_decidable S r b2 b1 -> @check_times_id_equals_plus_ann S
:= λ S r b1 b2 d, 
   match d with 
   | inl p => Certify_Times_Id_Equals_Plus_Ann (projT1 p)
   | inr _ => Certify_Not_Times_Id_Equals_Plus_Ann 
   end. 

  
End Translation.   