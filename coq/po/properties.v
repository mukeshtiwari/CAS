Require Import CAS.coq.common.compute. 

(* Note that some of the order-related properties are
  in brel_properties (such as reflexivity, transitivity)
*) 


Section ACAS.

Close Scope nat.   
Definition brel_antisymmetric (S : Type) (r1 : brel S) (r2 : brel S) := 
    ∀ s t : S, (r2 s t = true) → (r2 t s = true) → (r1 s t = true). 


Definition brel_not_antisymmetric (S : Type) (r1 : brel S) (r2 : brel S) 
(*   {s : S & {t : S & (r2 s t = true) * (r2 t s = true) * (r1 s t = false)}}. *) 
   := { z : S * S & match z with (s, t) =>  (r2 s t = true) * (r2 t s = true) * (r1 s t = false) end}. 

Definition brel_antisymmetric_decidable (S : Type) (r1 : brel S) (r2 : brel S) := 
   (brel_antisymmetric S r1 r2) + (brel_not_antisymmetric S r1 r2). 


(* top and bottom generalised for quasi-orders *)

Definition lte_equiv_unique (S : Type) (eq lte : brel S) (b : S) 
    := ∀ a : S, lte b a = true → lte a b = true → eq b a = true. 

Definition lte_equiv_not_unique (S : Type) (eq lte : brel S) (b : S) 
  := {a : S & (lte b a = true) * (lte a b = true) * (eq b a = false)}.

Definition brel_is_bottom (S : Type) (lte : brel S) (b : S) 
    := ∀ s : S, (lte b s = true).

Definition brel_not_is_bottom (S : Type) (lte : brel S) (b : S)
    := {s : S & lte b s = false }.

Definition brel_is_top (S : Type) (lte : brel S) (b : S) 
    := ∀ s : S, (lte s b = true).

Definition brel_not_is_top (S : Type) (lte : brel S) (b : S)
    := {s : S & lte s b = false }.

Definition brel_is_qo_bottom (S : Type) (eq lte : brel S) (b : S) 
    := (brel_is_bottom S lte b) * (lte_equiv_unique S eq lte b) . 

Definition brel_exists_qo_bottom (S : Type) (eq lte : brel S)
    := {b : S & brel_is_qo_bottom S eq lte b}.

Definition brel_not_is_qo_bottom (S : Type) (eq lte : brel S) (b : S)
    := (brel_not_is_bottom S lte b) + (lte_equiv_not_unique S eq lte b).

Definition brel_not_exists_qo_bottom (S : Type) (eq lte : brel S)
    := ∀ b : S, brel_not_is_qo_bottom S eq lte b.

Definition brel_exists_qo_bottom_decidable  (S : Type) (eq lte : brel S) := 
    (brel_exists_qo_bottom S eq lte) + (brel_not_exists_qo_bottom S eq lte). 


Definition brel_is_qo_top (S : Type) (eq lte : brel S) (b : S) 
    := (brel_is_top S lte b) * (lte_equiv_unique S eq lte b) . 

Definition brel_exists_qo_top (S : Type) (eq lte : brel S)
    := {b : S & brel_is_qo_top S eq lte b}.

Definition brel_not_is_qo_top (S : Type) (eq lte : brel S) (b : S)
    := (brel_not_is_top S lte b) + (lte_equiv_not_unique S eq lte b).

Definition brel_not_exists_qo_top (S : Type) (eq lte : brel S)
    := ∀ b : S, brel_not_is_qo_top S eq lte b.

Definition brel_exists_qo_top_decidable  (S : Type) (eq lte : brel S) := 
    (brel_exists_qo_top S eq lte) + (brel_not_exists_qo_top S eq lte). 


Definition brel_total (S : Type) (r : brel S) := 
    ∀ s t : S, (r s t = true) + (r t s = true). 

Definition brel_not_total (S : Type) (r : brel S) 
(*     {s : S & { t : S & (r s t = false) * (r t s = false)}}. *) 
   := { z : S * S & match z with (s, t) =>  (r s t = false) * (r t s = false) end}. 

Definition brel_total_decidable (S : Type) (r : brel S) := 
    (brel_total S r) + (brel_not_total S r).

Definition brel_irreflexive (S : Type) (r : brel S) := 
    ∀ s : S, r s s = false. 

Definition brel_not_irreflexive (S : Type) (r : brel S) := 
    {s : S & r s s = true}. 

Definition brel_irreflexive_decidable (S : Type) (r : brel S) := 
   (brel_irreflexive S r) + (brel_not_irreflexive S r). 


(*  Needed? 

Definition prefix_injective (S : Type) (n : nat) (f : nat -> S) (r : brel S), 
    := ∀ s t : nat, s <= n -> t <= n -> r (f s) (f t) = true -> s = t. 

Definition brel_finite (S : Type) (r : brel S) 
    := { n : nat & {f : nat -> S & ∀ s : S { m : nat & (m <= n) * (r (f m) s = true)}}}

Definition brel_not_finite (S : Type) (r : brel S) 
    := ∀ n : nat, ∀ f : nat -> S, {s : S &  ∀ m : nat , (m <= n)  -> (r (f m) s = false} ) }}

*) 

(* Needed for computing annihilator for minset_union. 
 
  Represent { f : unit -> list S & ∀ (s : S), {y : S, in_set eq (f tt) y = true * lte y s = true}} 
  as follows: 
*) 
Definition bottoms_finite (S : Type) (eq lte : brel S)
  := {p : (unit -> list S) * (S -> S) & match p with (f, w) =>  ∀ (s : S),  (in_set eq (f tt) (w s) = true) * (lte (w s) s = true) end}.

(* note : if we code bottoms_not_finite as the direct "negation" of bottoms_finite, then 
   bop_minset_union_not_exists_ann does not seem to go through ... ;-) 

Definition bottoms_not_finite (S : Type) (eq lte : brel S)
  := ∀ (X : list S), { s : S &  ∀ (y : S), (in_set eq X y = true) -> (lte y s = false)}.

*) 
Definition bottoms_not_finite (S : Type) (eq lte : brel S)
  := {f : (list S) -> S & ∀ (X : list S) (y : S), (in_set eq X y = true) -> (lte y (f X) = false)}.

Definition bottoms_finite_decidable  (S : Type) (eq lte : brel S) := (bottoms_finite S eq lte) + (bottoms_not_finite S eq lte).

(*  sanity check because the definitions have been changing a lot ... *) 
Lemma bottoms_finite_sanity_check (S : Type) (eq lte : brel S) : 
  bottoms_finite S eq lte -> bottoms_not_finite S eq lte -> (true = false).
Proof. intros [[f w] P] [g Q].
       destruct (P (g (f tt))) as [H0 H1]. 
       assert (H2 := Q (f tt) (w (g(f tt)))).
       assert (H3 := H2 H0). 
       rewrite H1 in H3. exact H3. 
Qed.


Definition brel_strict (S : Type) (r : brel S) (lt : brel S) := 
   ∀ s t : S, lt s t = true → r s t = false. 

Definition brel_not_strict (S : Type) (r : brel S) (lt : brel S) 
   := { z : S * S & match z with (s, t) => (lt s t = true) * (r s t = true) end}. 

Definition brel_strict_decidable (S : Type) (r : brel S) (lt : brel S) := 
   (brel_strict S r lt) + (brel_not_strict S r lt). 

Lemma brel_strict_covered : forall (S : Type) (r : brel S) (lt : brel S),  
   ((brel_strict S r lt) * (brel_not_strict S r lt)) -> False.  
Proof. intros S r lt [str [[s t] [L R]]]. rewrite (str s t L) in R. discriminate. Defined. 

(* 
    asymmetric iff  anti-symmetric  and irreflexive
               iff brel_strict S r r 
*) 
Definition brel_asymmetric (S : Type) (r : brel S) := 
   ∀ s t : S, r s t = true → r t s = false. 

Definition brel_not_asymmetric (S : Type) (r : brel S) 
   := { z : S * S & match z with (s, t) =>  (r s t = true) * (r t s = true) end}. 


Definition brel_asymmetric_decidable (S : Type) (r : brel S) := 
   (brel_asymmetric S r) + (brel_not_asymmetric S r). 



End ACAS.

Section CAS.

Inductive check_antisymmetric {S : Type} := 
| Certify_Antisymmetric : check_antisymmetric (S := S)
| Certify_Not_Antisymmetric : (S * S) → check_antisymmetric (S := S). 

Inductive assert_antisymmetric {S : Type} := 
| Assert_Antisymmetric : assert_antisymmetric (S := S). 

Inductive assert_not_antisymmetric {S : Type} := 
| Assert_Not_Antisymmetric : (S * S) → @assert_not_antisymmetric S. 
  

Inductive check_exists_qo_bottom {S : Type} := 
| Certify_Exists_Qo_Bottom : S → @check_exists_qo_bottom S
| Certify_Not_Exists_Qo_Bottom : @check_exists_qo_bottom S. 

Inductive assert_exists_qo_bottom {S : Type} := 
| Assert_Exists_Qo_Bottom : S → @assert_exists_qo_bottom S.
  
Inductive check_exists_qo_top {S : Type} := 
| Certify_Exists_Qo_Top : S → @check_exists_qo_top S
| Certify_Not_Exists_Qo_Top : @check_exists_qo_top S. 

Inductive assert_exists_qo_top {S : Type} := 
| Assert_Exists_Qo_Top : S → @assert_exists_qo_top S.
  
Inductive check_total {S : Type} := 
| Certify_Total : @check_total S
| Certify_Not_Total : (S * S) → @check_total S. 

Inductive assert_total {S : Type} := 
| Assert_Total : @assert_total S. 

Inductive assert_not_total {S : Type} := 
| Assert_Not_Total : (S * S) → @assert_not_total S. 


Inductive assert_asymmetric {S : Type} := 
| Assert_Asymmetric : assert_asymmetric (S := S). 

Inductive check_asymmetric {S : Type} := 
| Certify_Asymmetric : check_asymmetric (S := S)
| Certify_Not_Asymmetric : (S * S) → check_asymmetric (S := S). 


Inductive check_bottoms_finite {S : Type} := 
| Certify_Bottoms_Finite : ((unit -> list S) * (S -> S))  → check_bottoms_finite (S := S)
| Certify_Not_Bottoms_Finite : ((list S) -> S) -> check_bottoms_finite (S := S). 

End CAS.

Section Translation.

Definition p2c_antisymmetric_check : ∀ (S : Type) (eq lte : brel S), 
       brel_antisymmetric_decidable S eq lte -> @check_antisymmetric S 
:= λ S eq lte d, 
  match d with
   | inl _ => Certify_Antisymmetric 
   | inr p => Certify_Not_Antisymmetric (projT1 p)   
   end. 

Definition p2c_antisymmetric_assert : ∀ (S : Type) (eq lte : brel S), 
       brel_antisymmetric S eq lte -> @assert_antisymmetric S 
:= λ S eq lte NA, Assert_Antisymmetric. 

Definition p2c_not_antisymmetric_assert : ∀ (S : Type) (eq lte : brel S), 
       brel_not_antisymmetric S eq lte -> @assert_not_antisymmetric S 
:= λ S eq lte NA, Assert_Not_Antisymmetric (projT1 NA).    



Definition p2c_exists_qo_bottom_check : ∀ (S : Type) (eq lte : brel S), 
       brel_exists_qo_bottom_decidable S eq lte -> @check_exists_qo_bottom S 
:= λ S eq lte d, 
  match d with
   | inl p  => Certify_Exists_Qo_Bottom (projT1 p)   
   | inr _  => Certify_Not_Exists_Qo_Bottom
   end. 

Definition p2c_exists_qo_bottom_assert : ∀ (S : Type) (eq lte : brel S),
       brel_exists_qo_bottom S eq lte -> @assert_exists_qo_bottom S     
:= λ S eq lte B, Assert_Exists_Qo_Bottom (projT1 B).    


Definition p2c_exists_qo_top_check : ∀ (S : Type) (eq lte : brel S), 
       brel_exists_qo_top_decidable S eq lte -> @check_exists_qo_top S 
:= λ S eq lte d, 
  match d with
   | inl p  => Certify_Exists_Qo_Top (projT1 p)   
   | inr _  => Certify_Not_Exists_Qo_Top
   end. 

Definition p2c_exists_qo_top_assert : ∀ (S : Type) (eq lte : brel S),
       brel_exists_qo_top S eq lte -> @assert_exists_qo_top S     
:= λ S eq lte B, Assert_Exists_Qo_Top (projT1 B).    


Definition p2c_total_check : ∀ (S : Type) (lte : brel S), 
       brel_total_decidable S lte -> @check_total S 
:= λ S lte d, 
  match d with
   | inl _             => @Certify_Total S
   | inr p => Certify_Not_Total (projT1 p)
   end. 

Definition p2c_total_assert : ∀ (S : Type) (lte : brel S), 
       brel_total S lte -> @assert_total S 
:= λ S lte d, @Assert_Total S. 

Definition p2c_not_total_assert : ∀ (S : Type) (lte : brel S), 
       brel_not_total S lte -> @assert_not_total S 
:= λ S lte d, Assert_Not_Total (projT1 d).  


Definition p2c_bottoms_finite_check : ∀ (S : Type) (eq lte : brel S), 
       bottoms_finite_decidable S eq lte -> @check_bottoms_finite S 
:= λ S eq lte d, 
  match d with
   | inl p  => Certify_Bottoms_Finite (projT1 p)   
   | inr p  => Certify_Not_Bottoms_Finite (projT1 p)   
   end. 



  
End Translation.  