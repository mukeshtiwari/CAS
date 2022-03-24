Require Import CAS.coq.common.compute.

Section ACAS. 

Section LeftTransforms.

Close Scope nat.     
  
Definition ltr_congruence (L S : Type) (eqL : brel L) (eqS : brel S) (ltr : ltr_type L S) := 
   ∀ (l1 l2 : L) (s1 s2 : S) , eqL l1 l2 = true -> eqS s1 s2 = true -> eqS (ltr l1 s1) (ltr l2 s2) = true.

Definition ltr_is_right (L S : Type) (rS : brel S) (lt : ltr_type L S) 
    := ∀ (l : L) (s : S), rS (lt l s) s = true. 

Definition ltr_not_is_right (L S : Type) (rS : brel S) (lt : ltr_type L S) 
    := { z : L * S & match z with (l, s) =>  rS (lt l s) s = false end }. 

Definition ltr_is_right_decidable  (L S : Type) (rS : brel S) (lt : ltr_type L S) 
    := (ltr_is_right L S rS lt) + (ltr_not_is_right L S rS lt). 

Definition ltr_is_id (L S : Type) (rS : brel S) (lt : ltr_type L S) (l : L) 
    := ∀ s : S, (rS (lt l s) s = true).

Definition ltr_not_is_id (L S : Type) (rS : brel S) (lt : ltr_type L S) (l : L) 
    := {s : S & (rS (lt l s) s = false)}.

Definition ltr_exists_id (L S : Type) (rS : brel S) (lt : ltr_type L S) 
    := {l : L & ltr_is_id L S rS lt l}.

Definition ltr_not_exists_id (L S : Type) (rS : brel S) (lt : ltr_type L S) 
    := ∀ l : L, ltr_not_is_id L S rS lt l.

Definition ltr_exists_id_decidable (L S : Type) (rS : brel S) (lt : ltr_type L S) 
    := (ltr_exists_id L S rS lt) + (ltr_not_exists_id L S rS lt). 

Definition ltr_is_ann (L S : Type) (rS : brel S) (lt : ltr_type L S) (s : S) 
    := ∀ l : L, (rS (lt l s) s = true).

Definition ltr_not_is_ann (L S : Type) (rS : brel S) (lt : ltr_type L S) (s : S) 
    := {l : L & (rS (lt l s) s = false)}.

Definition ltr_exists_ann (L S : Type) (rS : brel S) (lt : ltr_type L S) 
    := {a : S & ltr_is_ann L S rS lt a}.

Definition ltr_not_exists_ann (L S : Type) (rS : brel S) (lt : ltr_type L S) 
    := ∀ a : S, ltr_not_is_ann L S rS lt a.

Definition ltr_exists_ann_decidable (L S : Type) (rS : brel S) (lt : ltr_type L S) 
    := (ltr_exists_ann L S rS lt) + (ltr_not_exists_ann L S rS lt). 

Definition ltr_left_cancellative (L S : Type) (rS : brel S) (lt : ltr_type L S) 
    := ∀ (l : L) (s1 s2 : S), rS (lt l s1) (lt l s2) = true -> rS s1 s2 = true.

Definition ltr_not_left_cancellative (L S : Type) (rS : brel S) (lt : ltr_type L S) 
   := { z : L * (S * S) & match z with (l, (s1, s2)) => (rS (lt l s1) (lt l s2) = true) * (rS s1 s2 = false) end }. 

Definition ltr_left_cancellative_decidable  (L S : Type) (rS : brel S) (lt : ltr_type L S) 
   := (ltr_left_cancellative L S rS lt) + (ltr_not_left_cancellative L S rS lt). 

(* properties below: needed ? *) 

Definition ltr_anti_right (L S : Type) (rS : brel S) (lt : ltr_type L S) := 
    ∀ (l : L) (s : S), rS (lt l s) s = false. 

Definition ltr_not_anti_right (L S : Type) (rS : brel S) (lt : ltr_type L S) 
   := { z : L * S & match z with (l, s) => rS (lt l s) s = true end }. 

Definition ltr_anti_right_decidable  (L S : Type) (rS : brel S) (lt : ltr_type L S) := 
    (ltr_anti_right L S rS lt) + (ltr_not_anti_right L S rS lt). 

Definition ltr_right_cancellative (L S : Type) (rL : brel L) (rS : brel S) (lt : ltr_type L S) 
    := ∀ (l1 l2 : L) (s : S), rS (lt l1 s) (lt l2 s) = true -> rL l1 l2 = true.

Definition ltr_not_right_cancellative (L S : Type) (rL : brel L) (rS : brel S) (lt : ltr_type L S) 
   := { z : L * (L * S) & match z with (l1, (l2, s)) => (rS (lt l1 s) (lt l2 s) = true) * (rL l1 l2 = false) end }. 

Definition ltr_right_cancellative_decidable  (L S : Type) (rL : brel L) (rS : brel S) (lt : ltr_type L S) 
   := (ltr_right_cancellative L S rL rS lt) + (ltr_not_right_cancellative L S rL rS lt). 


(* Condensed ("constant") *) 

Definition ltr_left_constant (L S : Type) (rS : brel S) (lt : ltr_type L S) 
    := ∀ (l : L) (s1 s2 : S), rS (lt l s1) (lt l s2) = true. 

Definition ltr_not_left_constant (L S : Type) (rS : brel S) (lt : ltr_type L S) 
   := { z : L * (S * S) & match z with (l, (s1, s2)) => rS (lt l s1) (lt l s2) = false  end }. 

Definition ltr_left_constant_decidable  (L S : Type) (rS : brel S) (lt : ltr_type L S) 
   := (ltr_left_constant L S rS lt) + (ltr_not_left_constant L S rS lt). 


Definition ltr_right_constant (L S : Type) (rS : brel S) (lt : ltr_type L S) 
    := ∀ (l1 l2 : L) (s : S), rS (lt l1 s) (lt l2 s) = true.            

Definition ltr_not_right_constant (L S : Type) (rS : brel S) (lt : ltr_type L S) 
   := { z : L * (L * S) & match z with (l1, (l2, s)) => rS (lt l1 s) (lt l2 s) = false  end }. 

Definition ltr_right_constant_decidable  (L S : Type) (rS : brel S) (lt : ltr_type L S) 
   := (ltr_right_constant L S rS lt) + (ltr_not_right_constant L S rS lt). 

End LeftTransforms.


Section RightTransforms.
  
Close Scope nat.

(*
Definition rtr_type (L S : Type) := S → L → S. 
*) 

Definition rtr_is_left (L S : Type) (rS : brel S) (rt : rtr_type L S) 
    := ∀ (l : L) (s : S), rS (rt s l) s = true. 

Definition rtr_not_is_left (L S : Type) (rS : brel S) (rt : rtr_type L S) 
    := { z : L * S & match z with (l, s) =>  rS (rt s l) s = false end }. 

Definition rtr_is_left_decidable  (L S : Type) (rS : brel S) (rt : rtr_type L S) 
    := (rtr_is_left L S rS rt) + (rtr_not_is_left L S rS rt). 

Definition rtr_is_left_id (L S : Type) (rS : brel S) (rt : rtr_type L S) (l : L) 
    := ∀ s : S, (rS (rt s l) s = true).

Definition rtr_not_is_left_id (L S : Type) (rS : brel S) (rt : rtr_type L S) (l : L) 
    := {s : S & (rS (rt s l) s = false)}.

Definition rtr_exists_left_id (L S : Type) (rS : brel S) (rt : rtr_type L S) 
    := {l : L & rtr_is_left_id L S rS rt l}.

Definition rtr_not_exists_left_id (L S : Type) (rS : brel S) (rt : rtr_type L S) 
    := ∀ l : L, rtr_not_is_left_id L S rS rt l.

Definition rtr_exists_left_id_decidable (L S : Type) (rS : brel S) (rt : rtr_type L S) 
    := (rtr_exists_left_id L S rS rt) + (rtr_not_exists_left_id L S rS rt). 

Definition rtr_right_cancellative (L S : Type) (rS : brel S) (rt : rtr_type L S) 
    := ∀ (l : L) (s1 s2 : S), rS (rt s1 l) (rt s2 l) = true -> rS s1 s2 = true.

Definition rtr_not_right_cancellative (L S : Type) (rS : brel S) (rt : rtr_type L S) 
   := { z : L * (S * S) & match z with (l, (s1, s2)) => (rS (rt s1 l) (rt s2 l) = true) * (rS s1 s2 = false) end }. 

Definition rtr_right_cancellative_decidable  (L S : Type) (rS : brel S) (rt : rtr_type L S) 
   := (rtr_right_cancellative L S rS rt) + (rtr_not_right_cancellative L S rS rt). 

(* properties below: needed ? *) 

Definition rtr_anti_left (L S : Type) (rS : brel S) (rt : rtr_type L S) := 
    ∀ (l : L) (s : S), rS (rt s l) s = false. 

Definition rtr_not_anti_left (L S : Type) (rS : brel S) (rt : rtr_type L S) 
   := { z : L * S & match z with (l, s) => rS (rt s l) s = true end }. 

Definition rtr_anti_left_decidable  (L S : Type) (rS : brel S) (rt : rtr_type L S) := 
    (rtr_anti_left L S rS rt) + (rtr_not_anti_left L S rS rt). 

(* Condensed ("constant") *) 

Definition rtr_right_constant (L S : Type) (rS : brel S) (rt : rtr_type L S) 
    := ∀ (l : L) (s1 s2 : S), rS (rt s1 l) (rt s2 l) = true. 

Definition rtr_not_right_constant (L S : Type) (rS : brel S) (rt : rtr_type L S) 
   := { z : L * (S * S) & match z with (l, (s1, s2)) => rS (rt s1 l) (rt s2 l) = false  end }. 

Definition rtr_right_constant_decidable  (L S : Type) (rS : brel S) (rt : rtr_type L S) 
   := (rtr_right_constant L S rS rt) + (rtr_not_right_constant L S rS rt). 

Definition rtr_left_constant (L S : Type) (rS : brel S) (rt : rtr_type L S) 
    := ∀ (l1 l2 : L) (s : S), rS (rt s l1) (rt s l2) = true.            

Definition rtr_not_left_constant (L S : Type) (rS : brel S) (rt : rtr_type L S) 
   := { z : L * (L * S) & match z with (l1, (l2, s)) => rS (rt s l1) (rt s l2) = false  end }. 

Definition rtr_left_constant_decidable  (L S : Type) (rS : brel S) (rt : rtr_type L S) 
   := (rtr_left_constant L S rS rt) + (rtr_not_left_constant L S rS rt). 
End RightTransforms.

End ACAS. 

Section CAS.

Inductive assert_ltr_congruence {L S : Type} := 
  Assert_Ltr_Congruence : @assert_ltr_congruence L S.

Inductive check_ltr_is_right {L S : Type} := 
| Certify_Ltr_Is_Right : @check_ltr_is_right L S
| Certify_Ltr_Not_Is_Right : (L * S) → @check_ltr_is_right L S.

Inductive check_ltr_exists_id {L S : Type} := 
| Certify_Ltr_Exists_Id : L → @check_ltr_exists_id L S
| Certify_Ltr_Not_Exists_Id : @check_ltr_exists_id L S.

Inductive check_ltr_exists_ann {L S : Type} := 
| Certify_Ltr_Exists_Ann : S → @check_ltr_exists_ann L S
| Certify_Ltr_Not_Exists_Ann : @check_ltr_exists_ann L S.

Inductive check_ltr_left_cancellative {L S : Type} := 
| Certify_Ltr_Left_Cancellative : @check_ltr_left_cancellative L S
| Certify_Ltr_Not_Left_Cancellative : (L * (S * S)) → @check_ltr_left_cancellative L S.

Inductive check_ltr_left_constant {L S : Type} := 
| Certify_Ltr_Left_Constant : @check_ltr_left_constant L S
| Certify_Ltr_Not_Left_Constant : (L * (S * S)) → @check_ltr_left_constant L S.

End CAS.

Section Translate.
  

Definition p2c_ltr_congruence (L S : Type) (eqL : brel L) (eqS : brel S) (ltr : ltr_type L S) 
    (p : ltr_congruence  L S eqL eqS ltr) : @assert_ltr_congruence L S := Assert_Ltr_Congruence. 
  
Definition p2c_ltr_is_right : ∀ (L S : Type) (lte : brel S) (ltr : ltr_type L S), 
       ltr_is_right_decidable L S lte ltr -> @check_ltr_is_right L S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Ltr_Is_Right
   | inr p => Certify_Ltr_Not_Is_Right (projT1 p)                                             
   end. 


Definition p2c_ltr_left_cancellative : ∀ (L S : Type) (lte : brel S) (ltr : ltr_type L S), 
       ltr_left_cancellative_decidable L S lte ltr -> @check_ltr_left_cancellative L S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Ltr_Left_Cancellative
   | inr p => Certify_Ltr_Not_Left_Cancellative (projT1 p)                                             
   end. 

Definition p2c_ltr_left_constant : ∀ (L S : Type) (lte : brel S) (ltr : ltr_type L S), 
       ltr_left_constant_decidable L S lte ltr -> @check_ltr_left_constant L S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Ltr_Left_Constant
   | inr p => Certify_Ltr_Not_Left_Constant (projT1 p)                                             
   end. 


Definition p2c_ltr_exists_id (L S : Type) (eq : brel S) (ltr : ltr_type L S) 
       (d : ltr_exists_id_decidable L S eq ltr) : @check_ltr_exists_id L S := 
   match d with 
   | inl p => Certify_Ltr_Exists_Id (projT1 p)                                             
   | inr _ => Certify_Ltr_Not_Exists_Id 
   end. 

Definition p2c_ltr_exists_ann (L S : Type) (eq : brel S) (ltr : ltr_type L S)
       (d : ltr_exists_ann_decidable L S eq ltr) : @check_ltr_exists_ann L S := 
   match d with 
   | inl p => Certify_Ltr_Exists_Ann (projT1 p)                                             
   | inr _ => Certify_Ltr_Not_Exists_Ann 
   end. 

End Translate.  
