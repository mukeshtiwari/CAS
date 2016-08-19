Require Import CAS.code.basic_types. 


(* unary ops *) 

Definition uop_bop_left_reduction (S : Type) (eq : brel S) (u : unary_op S) (b : binary_op S)
:= ∀ s t : S, eq (u (b s t)) (u (b (u s) t)) = true. 

Definition uop_bop_right_reduction (S : Type) (eq : brel S) (u : unary_op S) (b : binary_op S)
:= ∀ s t : S, eq (u (b s t)) (u (b s (u t))) = true. 

Definition uop_bop_reduction (S : Type) (eq : brel S) (u : unary_op S) (b : binary_op S)
:= ∀ s t : S, eq (u (b s t)) (u (b (u s) (u t))) = true. 

Definition uop_cancellative (S : Type) (r : brel S) (u : unary_op S)
    := ∀ s t : S, r (u s) (u t) = true -> r s t = true.

Definition uop_not_cancellative (S : Type) (r : brel S) (u : unary_op S)
   := { z : S * S & match z with (s, t) => (r (u s) (u t) = true) * (r s t = false) end }. 

Definition uop_cancellative_decidable  (S : Type) (r : brel S) (u : unary_op S) := 
    (uop_cancellative S r u) + (uop_not_cancellative S r u). 


Definition uop_preserves_brel (S : Type) (u : unary_op S) (r : brel S) := 
        ∀ (s : S), r (u s) s = true. 

Definition uop_injective (S : Type) (r : brel S) (u : unary_op S) := 
  ∀ s t : S, r (u s) (u t) = true -> r s t = true. 

(* Need this? *) 
Definition uop_congruence_positive (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ (s t : S), r s t = true -> r (u s) (u t) = true.

(* Need this?  THIS IS uop_injective_contrapositive !!!!  

constructively, if we have 

P = A -> B 

then we have 

Q = not B -> not A 


*) 
Definition uop_congruence_negative (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ (s t : S), r s t = false -> r (u s) (u t) = false.

Definition uop_congruence (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ (s t : S), r s t = true -> r (u s) (u t) = true.

Definition uop_uop_congruence (S : Type) (r : brel S) (u : unary_op S) (f : unary_op S) := 
   ∀ s t : S, r (u s) (u t) = true → r (u (f s)) (u (f t)) = true. 

Definition uop_idempotent (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ s : S, r (u (u s)) (u s) = true. 
 
Definition uop_not_trivial (S : Type) (r : brel S) (u : unary_op S)  
(*   {s : S & {t : S & r (u s) (u t) = false}}.  *) 
   := { z : S * S & match z with (s, t) => r (u s) (u t) = false end }. 

(* 
     u (s + t) = u ((u s) + t) 
or 
     u (s + t) <= u ((u s) + t)
*) 
Definition uop_bop_left_invariant (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S) := 
    ∀ (s t : S), r (u (b s t)) (u (b (u s) t)) = true. 

Definition uop_bop_right_invariant (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S) := 
    ∀ (s t : S), r (u (b s t)) (u (b s (u t))) = true. 

Definition uop_bop_invariant (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S) := 
    ∀ (s t : S), r (u (b s t)) (u (b (u s) (u t))) = true. 


(* NEED? 
Definition uop_congruence_right (S T : Type) (r : brel2 S T) (u : unary_op T) := 
   ∀ (s : S) (t : T), r s t = true -> r s (u t) = true.
*) 


Definition uop_preserves_left_positive (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ (s t : S), r s t = true -> r (u s) t = true.

Definition uop_preserves_left_negative (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ (s t : S), r s t = false -> r (u s) t = false.

Definition uop_preserves_right_positive (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ (s t : S), r s t = true -> r s (u t) = true.

Definition uop_preserves_right_negative (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ (s t : S), r s t = false -> r s (u t) = false.


Definition uop_brel2_preserves_left_positive (S T: Type) (r : brel2 S T) (u : unary_op S) := 
   ∀ (s : S) (t : T), r s t = true -> r (u s) t = true.

Definition uop_brel2_preserves_left_negative (S T : Type) (r : brel2 S T) (u : unary_op S) := 
   ∀ (s : S) (t : T), r s t = false -> r (u s) t = false.

(* Need? 
Definition uop_brel2_preserves_right (S T : Type) (r : brel2 S T) (u : unary_op T) := 
   ∀ (s : S) (t : T), r s t = true -> r s (u t) = true.

Definition uop_brel2_preserves_right_false (S T : Type) (r : brel2 S T) (u : unary_op T) := 
   ∀ (s : S) (t : T), r s t = false -> r s (u t) = false.
*) 

(*  
   u(s + t) + v   =  s + u (t + v)
*)  
Definition uop_bop_associative (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S) 
    := ∀ s t v : S, r (b (u (b s t)) v) (b s (u (b t v))) = true. 



