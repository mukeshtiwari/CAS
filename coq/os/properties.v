Require Import CAS.coq.common.compute.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.po.properties.

Close Scope nat. 
(* order, semigroup *) 

Definition os_left_monotone {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t u : S, lte t u = true -> lte (b s t) (b s u) = true. 

Definition os_not_left_monotone {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * (S * S) & match z with (s, (t, u)) => (lte t u = true) * (lte (b s t) (b s u) = false) end }. 

Definition os_left_monotone_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_left_monotone lte b) + (os_not_left_monotone lte b). 


Definition os_right_monotone {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t u : S, lte t u = true -> lte (b t s) (b u s) = true. 

Definition os_not_right_monotone {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * (S * S) & match z with (s, (t, u)) => (lte t u = true) * (lte (b t s) (b u s) = false) end }. 

Definition os_right_monotone_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_right_monotone lte b) + (os_not_right_monotone lte b). 


Definition os_left_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, lte s (b s t) = true. 

Definition os_not_left_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => lte s (b s t) = false end }. 

Definition os_left_increasing_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_left_increasing lte b) + (os_not_left_increasing lte b). 


Definition os_right_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, lte s (b t s) = true. 

Definition os_not_right_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => lte s (b t s) = false end }. 

Definition os_right_increasing_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_right_increasing lte b) + (os_not_right_increasing lte b). 


Definition os_left_strictly_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, (lte s (b s t) = true) * (lte (b s t) s = false). 

Definition os_not_left_strictly_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => (lte s (b s t) = false) + (lte (b s t) s = true)  end }. 

Definition os_left_strictly_increasing_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_left_strictly_increasing lte b) + (os_not_left_strictly_increasing lte b). 


Definition os_right_strictly_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, (lte s (b t s) = true) * (lte (b t s) s = false). 

Definition os_not_right_strictly_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => (lte s (b t s) = false) + (lte (b t s) s = true)  end }. 

Definition os_right_strictly_increasing_decidable {S : Type} (lte : brel S) (b : binary_op S)  
  := (os_right_strictly_increasing lte b) + (os_not_right_strictly_increasing lte b).


Definition os_left_strictly_monotone {S : Type} (lte : brel S) (b : binary_op S)  
  := ∀ s t u : S, lte t u = true -> lte u t = false ->
                  (lte (b s t) (b s u) = true) * (lte (b s u) (b s t) = false). 

Definition os_not_left_strictly_monotone {S : Type} (lte : brel S) (b : binary_op S)  
  := { z : S * (S * S) & match z with (s, (t, u)) =>
            (lte t u = true) * (lte u t = false) * ((lte (b s t) (b s u) = false) + (lte (b s u) (b s t) = true))end }. 

Definition os_left_strictly_monotone_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_left_strictly_monotone lte b) + (os_not_left_strictly_monotone lte b). 


Definition os_right_strictly_monotone {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t u : S, lte t u = true -> lte u t = false -> (lte (b t s) (b u s) = true) * (lte (b u s) (b t s) = false). 

Definition os_not_right_strictly_monotone {S : Type} (lte : brel S) (b : binary_op S)  
  := { z : S * (S * S) & match z with (s, (t, u)) =>
            (lte t u = true) * (lte u t = false) * ((lte (b t s) (b u s) = false) + (lte (b u s) (b t s) = true)) end }. 

Definition os_right_strictly_monotone_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_right_strictly_monotone lte b) + (os_not_right_strictly_monotone lte b). 


Definition os_bottom_equals_id {S : Type} (r lte : brel S) (b : binary_op S)
:= { i : S & (brel_is_bottom S lte i) * (bop_is_id S r b i)}. 

Definition os_qo_bottom_equals_id {S : Type} (r lte : brel S) (b : binary_op S)
:= { i : S & (brel_is_qo_bottom S r lte i) * (bop_is_id S r b i)}. 


Definition os_top_equals_ann {S : Type} (r lte : brel S) (b : binary_op S)
  := { i : S & (brel_is_top S lte i) * (bop_is_ann S r b i)}.


Definition os_not_top_equals_ann {S : Type} (r lte : brel S) (b : binary_op S)
:= ∀ i : S, (brel_not_is_top S lte i) + (bop_not_is_ann S r b i). 

Definition os_top_equals_ann_decidable  {S : Type} (r lte : brel S) (b : binary_op S) := 
    (os_top_equals_ann r lte b) + (os_not_top_equals_ann r lte b). 

Definition os_not_bottom_equals_id {S : Type} (r lte : brel S) (b : binary_op S) := 
   ∀ i : S, (brel_not_is_bottom S lte i) + (bop_not_is_id S r b i). 

Definition os_bottom_equals_id_decidable  {S : Type} (r lte : brel S) (b : binary_op S) := 
    (os_bottom_equals_id r lte b) + (os_not_bottom_equals_id r lte b). 

(* do the following belong in po/properties.v ? *) 
Definition is_lower_bound {S : Type} (lte : brel S) (a b c : S) :=  
     (lte c a = true) *  (lte c b = true). 

Definition is_upper_bound {S : Type} (lte : brel S) (a b c : S) :=  
     (lte a c = true) *  (lte b c = true). 

Definition is_glb {S : Type} (lte : brel S) (a b c : S) :=  
      (is_lower_bound lte a b c) *
          (∀ u : S, (is_lower_bound lte a b u) -> lte u c = true). 

Definition is_lub {S : Type} (lte : brel S) (a b c : S) :=  
      (is_upper_bound lte a b c) *
      (∀ u : S, (is_upper_bound lte a b u) -> lte c u = true).

Definition bop_is_glb {S : Type} (lte : brel S) (b : binary_op S) :=  ∀ s t : S,  is_glb lte s t (b s t).

Definition bop_is_lub {S : Type} (lte : brel S) (b : binary_op S) :=  ∀ s t : S,  is_lub lte s t (b s t).

Definition exists_glb {S : Type} (lte : brel S) := {b : binary_op S &  bop_is_glb lte b}.

Definition exists_lub {S : Type} (lte : brel S) := {b : binary_op S &  bop_is_lub lte b}.  
