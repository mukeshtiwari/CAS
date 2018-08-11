
Require Import CAS.coq.common.compute.
Close Scope nat. 
(*

Definition left_transform (L S : Type)  := L → S → S.  

*) 

Definition lt_congruence (L S : Type) (rL : brel L) (rS : brel S) (lt : left_transform L S) := 
   ∀ (l1 l2 : L) (s1 s2 : S), rL l1 l2 = true -> rS s1 s2 = true -> rS (lt l1 s1) (lt l2 s2) = true.

Definition lt_is_right (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := ∀ (l : L) (s : S), rS (lt l s) s = true. 

Definition lt_not_is_right (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := { z : L * S & match z with (l, s) =>  rS (lt l s) s = false end }. 

Definition lt_is_right_decidable  (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := (lt_is_right L S rS lt) + (lt_not_is_right L S rS lt). 

Definition lt_anti_right (L S : Type) (rS : brel S) (lt : left_transform L S) := 
    ∀ (l : L) (s : S), rS (lt l s) s = false. 

Definition lt_not_anti_right (L S : Type) (rS : brel S) (lt : left_transform L S) 
   := { z : L * S & match z with (l, s) => rS (lt l s) s = true end }. 

Definition lt_anti_right_decidable  (L S : Type) (rS : brel S) (lt : left_transform L S) := 
    (lt_anti_right L S rS lt) + (lt_not_anti_right L S rS lt). 

Definition lt_is_id (L S : Type) (rS : brel S) (lt : left_transform L S) (l : L) 
    := ∀ s : S, (rS (lt l s) s = true).

Definition lt_not_is_id (L S : Type) (rS : brel S) (lt : left_transform L S) (l : L) 
    := {s : S & (rS (lt l s) s = false)}.

Definition lt_exists_id (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := {l : L & lt_is_id L S rS lt l}.

Definition lt_not_exists_id (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := ∀ l : L, lt_not_is_id L S rS lt l.

Definition lt_exists_id_decidable (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := (lt_exists_id L S rS lt) + (lt_not_exists_id L S rS lt). 


(* Cancellativity *) 

Definition lt_left_cancellative (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := ∀ (l : L) (s1 s2 : S), rS (lt l s1) (lt l s2) = true -> rS s1 s2 = true.

Definition lt_not_left_cancellative (L S : Type) (rS : brel S) (lt : left_transform L S) 
   := { z : L * (S * S) & match z with (l, (s1, s2)) => (rS (lt l s1) (lt l s2) = true) * (rS s1 s2 = false) end }. 

Definition lt_left_cancellative_decidable  (L S : Type) (rS : brel S) (lt : left_transform L S) 
   := (lt_left_cancellative L S rS lt) + (lt_not_left_cancellative L S rS lt). 


Definition lt_right_cancellative (L S : Type) (rL : brel L) (rS : brel S) (lt : left_transform L S) 
    := ∀ (l1 l2 : L) (s : S), rS (lt l1 s) (lt l2 s) = true -> rL l1 l2 = true.

Definition lt_not_right_cancellative (L S : Type) (rL : brel L) (rS : brel S) (lt : left_transform L S) 
   := { z : L * (L * S) & match z with (l1, (l2, s)) => (rS (lt l1 s) (lt l2 s) = true) * (rL l1 l2 = false) end }. 

Definition lt_right_cancellative_decidable  (L S : Type) (rL : brel L) (rS : brel S) (lt : left_transform L S) 
   := (lt_right_cancellative L S rL rS lt) + (lt_not_right_cancellative L S rL rS lt). 


(* Condensed ("constant") *) 

Definition lt_left_constant (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := ∀ (l : L) (s1 s2 : S), rS (lt l s1) (lt l s2) = true. 

Definition lt_not_left_constant (L S : Type) (rS : brel S) (lt : left_transform L S) 
   := { z : L * (S * S) & match z with (l, (s1, s2)) => rS (lt l s1) (lt l s2) = false  end }. 

Definition lt_left_constant_decidable  (L S : Type) (rS : brel S) (lt : left_transform L S) 
   := (lt_left_constant L S rS lt) + (lt_not_left_constant L S rS lt). 


Definition lt_right_constant (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := ∀ (l1 l2 : L) (s : S), rS (lt l1 s) (lt l2 s) = true.            

Definition lt_not_right_constant (L S : Type) (rS : brel S) (lt : left_transform L S) 
   := { z : L * (L * S) & match z with (l1, (l2, s)) => rS (lt l1 s) (lt l2 s) = false  end }. 

Definition lt_right_constant_decidable  (L S : Type) (rS : brel S) (lt : left_transform L S) 
   := (lt_right_constant L S rS lt) + (lt_not_right_constant L S rS lt). 


