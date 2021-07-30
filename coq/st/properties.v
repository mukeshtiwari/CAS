Require Import CAS.coq.common.compute.
Require Import CAS.coq.sg.properties. 

Close Scope nat. 

Definition slt_distributive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := ∀ (l : L) (t u : S), r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = true. 

Definition slt_not_distributive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * (S * S) & match z with (l, (t, u)) => r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = false end }. 

Definition slt_distributive_decidable (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (slt_distributive L S r add ltr) + (slt_not_distributive L S r add ltr). 
 
Definition slt_absorptive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), r s (add s (ltr l s)) = true.

Definition slt_not_absorptive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * S  & match z with (l, s) =>  r s (add s (ltr l s)) = false end }. 

Definition slt_absorptive_decidable (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (slt_absorptive L S r add ltr) + (slt_not_absorptive L S r add ltr). 


Definition slt_strictly_absorptive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), ((r s (add s (ltr l s)) = true) * (r (ltr l s) (add s (ltr l s)) = false)).

Definition slt_not_strictly_absorptive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * S  & match z with (l, s) =>  ((r s (add s (ltr l s)) = false)  +  (r s (add (ltr l s) (ltr l s)) = true)) end }. 

Definition slt_strictly_absorptive_decidable (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (slt_strictly_absorptive L S r add ltr) + (slt_not_strictly_absorptive L S r add ltr). 



(*
Definition slt_distributive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := ∀ (l : L) (t u : S), r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = true. 

Definition slt_not_distributive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * (S * S) & match z with (l, (t, u)) => r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = false end }. 

Definition slt_distributive_decidable (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (slt_distributive S L r add ltr) + (slt_not_distributive S L r add ltr). 
 
Definition slt_absorptive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), r s (add s (ltr l s)) = true.

Definition slt_not_absorptive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * S  & match z with (l, s) =>  r s (add s (ltr l s)) = false end }. 

Definition slt_absorptive_decidable (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (slt_absorptive S L r add ltr) + (slt_not_absorptive S L r add ltr). 


Definition slt_strictly_absorptive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), (bop_not_is_id S r add s) -> ((r s (add s (ltr l s)) = true) * (r s (add s (ltr l s)) = false)).

Definition slt_not_strictly_absorptive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * S  & match z with (l, s) =>  (bop_not_is_id S r add s) * ((r s (add s (ltr l s)) = false)  +  (r s (add s (ltr l s)) = true)) end }. 

Definition slt_strictly_absorptive_decidable (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (slt_strictly_absorptive S L r add ltr) + (slt_not_strictly_absorptive S L r add ltr). 
*)