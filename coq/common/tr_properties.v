
Require Import CAS.coq.common.compute.

Section LeftTransforms.
  
Close Scope nat.

(*
Definition left_transform (L S : Type)  := L → S → S.  
*) 

Definition ltr_congruence (L S : Type) (rL : brel L) (rS : brel S) (lt : left_transform L S) := 
   ∀ (l1 l2 : L) (s1 s2 : S), rL l1 l2 = true -> rS s1 s2 = true -> rS (lt l1 s1) (lt l2 s2) = true.

Definition ltr_is_right (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := ∀ (l : L) (s : S), rS (lt l s) s = true. 

Definition ltr_not_is_right (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := { z : L * S & match z with (l, s) =>  rS (lt l s) s = false end }. 

Definition ltr_is_right_decidable  (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := (ltr_is_right L S rS lt) + (ltr_not_is_right L S rS lt). 

Definition ltr_is_id (L S : Type) (rS : brel S) (lt : left_transform L S) (l : L) 
    := ∀ s : S, (rS (lt l s) s = true).

Definition ltr_not_is_id (L S : Type) (rS : brel S) (lt : left_transform L S) (l : L) 
    := {s : S & (rS (lt l s) s = false)}.

Definition ltr_exists_id (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := {l : L & ltr_is_id L S rS lt l}.

Definition ltr_not_exists_id (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := ∀ l : L, ltr_not_is_id L S rS lt l.

Definition ltr_exists_id_decidable (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := (ltr_exists_id L S rS lt) + (ltr_not_exists_id L S rS lt). 

Definition ltr_left_cancellative (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := ∀ (l : L) (s1 s2 : S), rS (lt l s1) (lt l s2) = true -> rS s1 s2 = true.

Definition ltr_not_left_cancellative (L S : Type) (rS : brel S) (lt : left_transform L S) 
   := { z : L * (S * S) & match z with (l, (s1, s2)) => (rS (lt l s1) (lt l s2) = true) * (rS s1 s2 = false) end }. 

Definition ltr_left_cancellative_decidable  (L S : Type) (rS : brel S) (lt : left_transform L S) 
   := (ltr_left_cancellative L S rS lt) + (ltr_not_left_cancellative L S rS lt). 


(* properties below: needed ? *) 

Definition ltr_anti_right (L S : Type) (rS : brel S) (lt : left_transform L S) := 
    ∀ (l : L) (s : S), rS (lt l s) s = false. 

Definition ltr_not_anti_right (L S : Type) (rS : brel S) (lt : left_transform L S) 
   := { z : L * S & match z with (l, s) => rS (lt l s) s = true end }. 

Definition ltr_anti_right_decidable  (L S : Type) (rS : brel S) (lt : left_transform L S) := 
    (ltr_anti_right L S rS lt) + (ltr_not_anti_right L S rS lt). 

Definition ltr_right_cancellative (L S : Type) (rL : brel L) (rS : brel S) (lt : left_transform L S) 
    := ∀ (l1 l2 : L) (s : S), rS (lt l1 s) (lt l2 s) = true -> rL l1 l2 = true.

Definition ltr_not_right_cancellative (L S : Type) (rL : brel L) (rS : brel S) (lt : left_transform L S) 
   := { z : L * (L * S) & match z with (l1, (l2, s)) => (rS (lt l1 s) (lt l2 s) = true) * (rL l1 l2 = false) end }. 

Definition ltr_right_cancellative_decidable  (L S : Type) (rL : brel L) (rS : brel S) (lt : left_transform L S) 
   := (ltr_right_cancellative L S rL rS lt) + (ltr_not_right_cancellative L S rL rS lt). 


(* Condensed ("constant") *) 

Definition ltr_left_constant (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := ∀ (l : L) (s1 s2 : S), rS (lt l s1) (lt l s2) = true. 

Definition ltr_not_left_constant (L S : Type) (rS : brel S) (lt : left_transform L S) 
   := { z : L * (S * S) & match z with (l, (s1, s2)) => rS (lt l s1) (lt l s2) = false  end }. 

Definition ltr_left_constant_decidable  (L S : Type) (rS : brel S) (lt : left_transform L S) 
   := (ltr_left_constant L S rS lt) + (ltr_not_left_constant L S rS lt). 


Definition ltr_right_constant (L S : Type) (rS : brel S) (lt : left_transform L S) 
    := ∀ (l1 l2 : L) (s : S), rS (lt l1 s) (lt l2 s) = true.            

Definition ltr_not_right_constant (L S : Type) (rS : brel S) (lt : left_transform L S) 
   := { z : L * (L * S) & match z with (l1, (l2, s)) => rS (lt l1 s) (lt l2 s) = false  end }. 

Definition ltr_right_constant_decidable  (L S : Type) (rS : brel S) (lt : left_transform L S) 
   := (ltr_right_constant L S rS lt) + (ltr_not_right_constant L S rS lt). 

End LeftTransforms.


Section RightTransforms.
  
Close Scope nat.

(*
Definition right_transform (L S : Type) := S → L → S. 
*) 

Definition rtr_congruence (L S : Type) (rL : brel L) (rS : brel S) (rt : right_transform L S) := 
   ∀ (l1 l2 : L) (s1 s2 : S), rL l1 l2 = true -> rS s1 s2 = true -> rS (rt s1 l1) (rt s2 l2) = true.

Definition rtr_is_left (L S : Type) (rS : brel S) (rt : right_transform L S) 
    := ∀ (l : L) (s : S), rS (rt s l) s = true. 

Definition rtr_not_is_left (L S : Type) (rS : brel S) (rt : right_transform L S) 
    := { z : L * S & match z with (l, s) =>  rS (rt s l) s = false end }. 

Definition rtr_is_left_decidable  (L S : Type) (rS : brel S) (rt : right_transform L S) 
    := (rtr_is_left L S rS rt) + (rtr_not_is_left L S rS rt). 

Definition rtr_is_left_id (L S : Type) (rS : brel S) (rt : right_transform L S) (l : L) 
    := ∀ s : S, (rS (rt s l) s = true).

Definition rtr_not_is_left_id (L S : Type) (rS : brel S) (rt : right_transform L S) (l : L) 
    := {s : S & (rS (rt s l) s = false)}.

Definition rtr_exists_left_id (L S : Type) (rS : brel S) (rt : right_transform L S) 
    := {l : L & rtr_is_left_id L S rS rt l}.

Definition rtr_not_exists_left_id (L S : Type) (rS : brel S) (rt : right_transform L S) 
    := ∀ l : L, rtr_not_is_left_id L S rS rt l.

Definition rtr_exists_left_id_decidable (L S : Type) (rS : brel S) (rt : right_transform L S) 
    := (rtr_exists_left_id L S rS rt) + (rtr_not_exists_left_id L S rS rt). 

Definition rtr_right_cancellative (L S : Type) (rS : brel S) (rt : right_transform L S) 
    := ∀ (l : L) (s1 s2 : S), rS (rt s1 l) (rt s2 l) = true -> rS s1 s2 = true.

Definition rtr_not_right_cancellative (L S : Type) (rS : brel S) (rt : right_transform L S) 
   := { z : L * (S * S) & match z with (l, (s1, s2)) => (rS (rt s1 l) (rt s2 l) = true) * (rS s1 s2 = false) end }. 

Definition rtr_right_cancellative_decidable  (L S : Type) (rS : brel S) (rt : right_transform L S) 
   := (rtr_right_cancellative L S rS rt) + (rtr_not_right_cancellative L S rS rt). 

(* properties below: needed ? *) 

Definition rtr_anti_left (L S : Type) (rS : brel S) (rt : right_transform L S) := 
    ∀ (l : L) (s : S), rS (rt s l) s = false. 

Definition rtr_not_anti_left (L S : Type) (rS : brel S) (rt : right_transform L S) 
   := { z : L * S & match z with (l, s) => rS (rt s l) s = true end }. 

Definition rtr_anti_left_decidable  (L S : Type) (rS : brel S) (rt : right_transform L S) := 
    (rtr_anti_left L S rS rt) + (rtr_not_anti_left L S rS rt). 

(* Condensed ("constant") *) 

Definition rtr_right_constant (L S : Type) (rS : brel S) (rt : right_transform L S) 
    := ∀ (l : L) (s1 s2 : S), rS (rt s1 l) (rt s2 l) = true. 

Definition rtr_not_right_constant (L S : Type) (rS : brel S) (rt : right_transform L S) 
   := { z : L * (S * S) & match z with (l, (s1, s2)) => rS (rt s1 l) (rt s2 l) = false  end }. 

Definition rtr_right_constant_decidable  (L S : Type) (rS : brel S) (rt : right_transform L S) 
   := (rtr_right_constant L S rS rt) + (rtr_not_right_constant L S rS rt). 

Definition rtr_left_constant (L S : Type) (rS : brel S) (rt : right_transform L S) 
    := ∀ (l1 l2 : L) (s : S), rS (rt s l1) (rt s l2) = true.            

Definition rtr_not_left_constant (L S : Type) (rS : brel S) (rt : right_transform L S) 
   := { z : L * (L * S) & match z with (l1, (l2, s)) => rS (rt s l1) (rt s l2) = false  end }. 

Definition rtr_left_constant_decidable  (L S : Type) (rS : brel S) (rt : right_transform L S) 
   := (rtr_left_constant L S rS rt) + (rtr_not_left_constant L S rS rt). 

End RightTransforms.