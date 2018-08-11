Require Import CAS.coq.common.compute.
Close Scope nat. 
(* order, semigroup *) 

Definition os_left_monotone (S : Type) (lte : brel S) (b : binary_op S)  
   := ∀ s t u : S, lte t u = true -> lte (b s t) (b s u) = true. 

Definition os_not_left_monotone (S : Type) (lte : brel S) (b : binary_op S)  
   := { z : S * (S * S) & match z with (s, (t, u)) => (lte t u = true) * (lte (b s t) (b s u) = false) end }. 

Definition os_left_monotone_decidable (S : Type) (lte : brel S) (b : binary_op S)  
   := (os_left_monotone S lte b) + (os_not_left_monotone S lte b). 


Definition os_right_monotone (S : Type) (lte : brel S) (b : binary_op S)  
   := ∀ s t u : S, lte t u = true -> lte (b t s) (b u s) = true. 

Definition os_not_right_monotone (S : Type) (lte : brel S) (b : binary_op S)  
   := { z : S * (S * S) & match z with (s, (t, u)) => (lte t u = true) * (lte (b t s) (b u s) = false) end }. 

Definition os_right_monotone_decidable (S : Type) (lte : brel S) (b : binary_op S)  
   := (os_right_monotone S lte b) + (os_not_right_monotone S lte b). 


Definition os_left_increasing (S : Type) (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, lte s (b s t) = true. 

Definition os_not_left_increasing (S : Type) (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => lte s (b s t) = false end }. 

Definition os_left_increasing_decidable (S : Type) (lte : brel S) (b : binary_op S)  
   := (os_left_increasing S lte b) + (os_not_left_increasing S lte b). 


Definition os_right_increasing (S : Type) (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, lte s (b t s) = true. 

Definition os_not_right_increasing (S : Type) (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => lte s (b t s) = false end }. 

Definition os_right_increasing_decidable (S : Type) (lte : brel S) (b : binary_op S)  
   := (os_right_increasing S lte b) + (os_not_right_increasing S lte b). 

Definition is_lower_bound (S : Type) (lte : brel S) (a b c : S) :=  
     (lte c a = true) *  (lte c b = true). 

Definition is_upper_bound (S : Type) (lte : brel S) (a b c : S) :=  
     (lte a c = true) *  (lte b c = true). 

Definition os_is_glb (S : Type) (lte : brel S) (b : binary_op S)  := 
   ∀ s t : S, (is_lower_bound S lte s t (b s t)) *
              (∀ u : S, (is_lower_bound S lte s t u) -> lte u (b s t) = true). 


Definition os_is_lub (S : Type) (lte : brel S) (b : binary_op S)  := 
   ∀ s t : S, (is_upper_bound S lte s t (b s t)) *
              (∀ u : S, (is_upper_bound S lte s t u) -> lte (b s t) u = true). 

